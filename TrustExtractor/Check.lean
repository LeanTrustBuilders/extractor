import Lean
import TrustExtractor.Util

/-!
# Check 2: Lean's kernel checks the closures a dataset records

`dependency-testing.md` §9 in LeanTrustBuilders/design. For each project declaration D of a dataset,
Lean's kernel checks D in an environment that holds:
* the libraries underneath the project;
* the project's constants that are not nodes of the dataset (compiler helpers, and whatever else the
  dataset looks through);
* of the project's nodes, only those in D's closure along one notion (`meaning` or `term`), as the
  dataset's edges draw it.

A constant the kernel needs and the closure lacks is reported as **missing**. The kernel stops at
the first unknown constant, so the check adds it and runs again, until D checks, to report them all.

**The verdict comes from outside the suite.** The check reads the dataset's edges, not MeaningGraph's
tables, and erases proofs with a pass of its own. What it decides for itself is only which constants
go together (a *block*: an inductive type with its constructors and recursors, or one constant) and
which are helpers (the project's constants that are not nodes), so a missing node cannot slip
through.

**The project's constants are renamed** (`_kc.<i>`) in everything the check adds or checks. The
imported environment still holds them under their own names, and a reference to one that the check
did not add would otherwise find it there.

**Proofs are erased** for `meaning`, whose closure does not follow proofs: an argument whose expected
type is a proposition becomes `sorryAx` of that type, a let-bound proof likewise, and theorems are
added as axioms. For `term`, values are kept whole and theorems are checked with their proofs; the
theorems of the closure are still added as axioms, so each declaration is checked once, in its own
turn.

It also reports what D **mentions**, through helpers, that its closure lacks (`unlisted`): stricter
than the kernel, which only looks at what it unfolds. Both come from this module's own walk.

It proves sufficiency, not minimality, and says nothing about notation and coercions, which the
kernel does not see.
-/

namespace TrustExtractor.Check

open Lean Meta

/-- Inserts a constant into a kernel environment without checking it. This is
`Kernel.Environment.add`, which is private. -/
@[extern "lean_environment_add"]
opaque kernelAdd (env : Kernel.Environment) (info : ConstantInfo) : Kernel.Environment

/-- What to check. -/
structure Config where
  /-- The project's root module prefix, e.g. `TauCeti`. -/
  root : Name
  /-- The dataset, extracted from the project as built in the working directory. -/
  dataset : System.FilePath := "dataset"
  /-- The notion whose closures are checked: `meaning` or `term`. -/
  notion : String := "meaning"
  /-- Modules to import, and whose declarations to check. Empty means the dataset's modules. -/
  modules : Array Name := #[]
  /-- Declarations to check. Empty means every project node of the modules. -/
  decls : Array String := #[]
  /-- Edges to leave out, by name (source, target): for testing the check itself. -/
  dropEdges : Array (String × String) := #[]
  /-- How many checks to run at once. -/
  jobs : Nat := 1
  /-- The kernel's heartbeat limit per check, in thousands (0: none). -/
  heartbeats : Nat := 0
  /-- Whether to write the result into the dataset, as a facet. -/
  write : Bool := true

/-! ## The dataset's graph -/

/-- The part of a dataset the check reads. -/
structure Graph where
  names : Array String
  project : Array Bool
  modules : Array String
  ids : Std.HashMap String Nat
  succ : Array (Array Nat)

private def u32At (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat ||| (b[i+1]!.toNat <<< 8) ||| (b[i+2]!.toNat <<< 16) ||| (b[i+3]!.toNat <<< 24)

def readGraph (dir : System.FilePath) (notion : String) (drop : Array (String × String)) :
    IO Graph := do
  let mut names := #[]
  let mut project := #[]
  let mut modules := #[]
  let mut ids : Std.HashMap String Nat := {}
  for line in ← IO.FS.lines (dir / "decls.jsonl") do
    if line.isEmpty then continue
    let j ← IO.ofExcept (Json.parse line)
    let id ← IO.ofExcept (j.getObjValAs? Nat "id")
    let name ← IO.ofExcept (j.getObjValAs? String "name")
    unless id == names.size do throw <| IO.userError s!"decls.jsonl: id {id} out of order"
    ids := ids.insert name id
    names := names.push name
    project := project.push ((j.getObjValAs? String "scope").toOption == some "project")
    modules := modules.push ((j.getObjValAs? String "module").toOption.getD "")
  let dropped : Std.HashSet (Nat × Nat) := drop.foldl (init := {}) fun s (a, b) =>
    match ids.get? a, ids.get? b with
    | some i, some k => s.insert (i, k)
    | _, _ => s
  let file := dir / "edges" / s!"{notion}.bin"
  unless ← file.pathExists do throw <| IO.userError s!"the dataset has no `{notion}` edges ({file})"
  let bytes ← IO.FS.readBinFile file
  let mut succ : Array (Array Nat) := Array.replicate names.size #[]
  for k in [0:bytes.size / 8] do
    let s := u32At bytes (8 * k)
    let t := u32At bytes (8 * k + 4)
    if s < names.size && t < names.size && !dropped.contains (s, t) then
      succ := succ.modify s (·.push t)
  return { names, project, modules, ids, succ }

/-- The nodes reachable from `i`, `i` excluded unless it is on a cycle. -/
def Graph.closure (g : Graph) (i : Nat) : Array Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut out := #[]
  let mut stack := g.succ[i]!
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    if seen.contains x then continue
    seen := seen.insert x
    out := out.push x
    stack := stack ++ g.succ[x]!
  return out

/-! ## Erasing proofs -/

abbrev EraseM := StateRefT (Std.HashMap ExprStructEq Expr) MetaM

/-- A proof of `type`, which the kernel takes on trust: `sorryAx type`. -/
def mkSorry (type : Expr) : Expr :=
  mkApp2 (mkConst ``sorryAx [Level.zero]) type (mkConst ``Bool.false)

/-- `e`, which is not itself a proof, with its proofs erased: every argument whose expected type is
a proposition (unless it is a local variable), and every let-bound value whose type is, becomes
`sorryAx` of that type (itself erased). The expected type of an argument comes from the type of the function applied, so the
erased term mentions nothing its proofs alone mentioned. -/
partial def erase (e : Expr) : EraseM Expr := do
  match e with
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .lit .. | .const .. => return e
  | _ =>
  if let some r := (← get).get? e then return r
  let r ← match e with
    | .app .. => do
      let f := e.getAppFn
      let mut out ← erase f
      let mut ty ← inferType f
      for a in e.getAppArgs do
        unless ty.isForall do ty ← whnf ty
        let .forallE _ d b _ := ty | throwError "erase: expected a function type, got{indentExpr ty}"
        -- A proof that is a local variable is kept: it mentions nothing, and an inductive type's
        -- constructors must apply it to its parameters, `Prop` ones included, as they are.
        let a' ← if !a.isFVar && (← isProp d) then do pure (mkSorry (← erase d)) else erase a
        out := .app out a'
        ty := b.instantiate1 a
      pure out
    | .lam n t b bi => do
      let t' ← erase t
      withLocalDecl n bi t fun x => do
        return .lam n t' ((← erase (b.instantiate1 x)).abstract #[x]) bi
    | .forallE n t b bi => do
      let t' ← erase t
      withLocalDecl n bi t fun x => do
        return .forallE n t' ((← erase (b.instantiate1 x)).abstract #[x]) bi
    | .letE n t v b nondep => do
      let t' ← erase t
      let v' ← if ← isProp t then pure (mkSorry t') else erase v
      withLetDecl n t v (nondep := nondep) fun x => do
        return .letE n t' v' ((← erase (b.instantiate1 x)).abstract #[x]) nondep
    | .mdata m b => pure (.mdata m (← erase b))
    | .proj s i b => pure (.proj s i (← erase b))
    | _ => pure e
  modify (·.insert e r)
  return r

/-- Renames the project's constants in `e`, and the structures its projections name. -/
partial def rename (ren : Std.HashMap Name Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => (ren.get? n).map (.const · us)
    | .proj s i b => (ren.get? s).map fun s' => .proj s' i (rename ren b)
    | _ => none

/-- The constants `e` mentions, and the structures its projections name. -/
def mentioned (e : Expr) (acc : IO.Ref NameSet) : MetaM Unit :=
  e.forEach fun
    | .const n _ => acc.modify (·.insert n)
    | .proj s _ _ => acc.modify (·.insert s)
    | _ => pure ()

/-! ## Blocks -/

/-- A project constant as the check adds it, or checks it: an inductive type with its constructors
and recursors, or one constant. -/
structure Block where
  /-- The names of its constants. -/
  names : Array Name
  /-- What is added to the environment when the block is in a closure: renamed, and under
  `meaning` erased, with theorems as axioms. -/
  consts : Array ConstantInfo := #[]
  /-- What the kernel checks when the block is the declaration checked. None: nothing to check. -/
  decl? : Option Declaration := none
  /-- Why the block is not checked, or was not erased. -/
  note : Option String := none
  /-- The project constants its constants mention, by block. -/
  mentions : Array Name := #[]
deriving Inhabited

/-- The block a project constant belongs to, named by its first constant. -/
def blockOf (env : Environment) (n : Name) : Name :=
  match env.find? n with
  | some (.ctorInfo v) =>
    match env.find? v.induct with
    | some (.inductInfo iv) => iv.all.headD v.induct
    | _ => v.induct
  | some (.recInfo v) => v.all.headD n
  | some (.inductInfo v) => v.all.headD n
  | _ => n

/-- `ConstantInfo` with another name, for the constants that do not otherwise need rebuilding. -/
def _root_.Lean.ConstantInfo.updateName? (info : ConstantInfo) (n : Name) : Option ConstantInfo :=
  match info with
  | .quotInfo v => some (.quotInfo { v with name := n })
  | .ctorInfo v => some (.ctorInfo { v with name := n })
  | .recInfo v => some (.recInfo { v with name := n })
  | _ => none

/-- Builds the block named `b`. `ren` renames every project constant; `erase?` is true for
`meaning`. -/
def mkBlock (ren : Std.HashMap Name Name) (erase? : Bool) (b : Name) : MetaM Block := do
  let r (n : Name) : Name := ren.getD n n
  let R := rename ren
  let er (e : Expr) : MetaM Expr := do
    if erase? then return (← (erase e).run' {}) else return e
  match ← getConstInfo b with
  | .inductInfo v =>
    -- As `Lean.Replay` rebuilds a block: its types and their constructors, which the kernel checks
    -- together and from which it generates the recursors. Under `meaning` their proofs are erased
    -- like any other's, recursors included: a constructor's type can hold a proof (an instance of a
    -- `Prop` class), and comparing it with an erased argument would make the kernel look up what
    -- that proof mentions. Where an erased and an unerased proof meet, proof irrelevance bridges them.
    let inds ← v.all.mapM getConstInfoInduct
    let ctors ← inds.flatMap (·.ctors) |>.mapM getConstInfoCtor
    let env ← getEnv
    let recNames := v.all.map mkRecName ++
      (List.range v.numNested).map fun i => v.all.headD b |>.str s!"rec_{i + 1}"
    let recs := recNames.filterMap fun n => match env.find? n with
      | some (.recInfo rv) => some rv
      | _ => none
    let indTypes ← inds.mapM (er ·.type)
    let ctorTypes ← ctors.mapM (er ·.type)
    let recTypes ← recs.mapM (er ·.type)
    let recRules ← recs.mapM fun rv => rv.rules.mapM fun rl => return { rl with ctor := r rl.ctor, rhs := R (← er rl.rhs) }
    let consts : Array ConstantInfo :=
      ((inds.zip indTypes).map fun (i, t) => ConstantInfo.inductInfo { i with
        name := r i.name, type := R t, all := i.all.map r, ctors := i.ctors.map r }).toArray ++
      ((ctors.zip ctorTypes).map fun (c, t) => ConstantInfo.ctorInfo { c with
        name := r c.name, type := R t, induct := r c.induct }).toArray ++
      (((recs.zip recTypes).zip recRules).map fun ((rv, t), rules) => ConstantInfo.recInfo { rv with
        name := r rv.name, type := R t, all := rv.all.map r, rules }).toArray
    let ctorType : Std.HashMap Name Expr := (ctors.zip ctorTypes).foldl (fun m (c, t) => m.insert c.name t) {}
    let types : List InductiveType := (inds.zip indTypes).map fun (i, t) =>
      { name := r i.name, type := R t
        ctors := (ctors.filter (·.induct == i.name)).map fun c =>
          { name := r c.name, type := R (ctorType.getD c.name c.type) } }
    let names := (inds.map (·.name) ++ ctors.map (·.name) ++ recs.map (·.name)).toArray
    return { names, consts, decl? := some (.inductDecl v.levelParams v.numParams types v.isUnsafe) }
  | .defnInfo v =>
    if v.safety == .unsafe then
      let d : DefinitionVal := { v with name := r b, type := R v.type, value := R v.value, all := [r b] }
      return { names := #[b], consts := #[.defnInfo d], note := some "unsafe" }
    let type ← er v.type
    if ← isProp v.type then
      let ax : AxiomVal := { name := r b, levelParams := v.levelParams, type := R type, isUnsafe := false }
      let decl := if erase? then .axiomDecl ax else
        .defnDecl { v with name := r b, type := R type, value := R v.value, all := [r b] }
      return { names := #[b], consts := #[.axiomInfo ax], decl? := some decl }
    let d : DefinitionVal := { v with name := r b, type := R type, value := R (← er v.value), all := [r b] }
    return { names := #[b], consts := #[.defnInfo d], decl? := some (.defnDecl d) }
  | .thmInfo v =>
    let type ← er v.type
    let ax : AxiomVal := { name := r b, levelParams := v.levelParams, type := R type, isUnsafe := false }
    let decl := if erase? then .axiomDecl ax else
      .thmDecl { v with name := r b, type := R type, value := R v.value, all := [r b] }
    return { names := #[b], consts := #[.axiomInfo ax], decl? := some decl }
  | .opaqueInfo v =>
    let type ← er v.type
    if ← isProp v.type then
      let ax : AxiomVal := { name := r b, levelParams := v.levelParams, type := R type, isUnsafe := v.isUnsafe }
      return { names := #[b], consts := #[.axiomInfo ax], decl? := some (.axiomDecl ax) }
    let o : OpaqueVal := { v with name := r b, type := R type, value := R (← er v.value), all := [r b] }
    return { names := #[b], consts := #[.opaqueInfo o],
             decl? := if v.isUnsafe then none else some (.opaqueDecl o),
             note := if v.isUnsafe then some "unsafe" else none }
  | .axiomInfo v =>
    let ax : AxiomVal := { v with name := r b, type := R (← er v.type) }
    return { names := #[b], consts := #[.axiomInfo ax], decl? := some (.axiomDecl ax) }
  | info =>
    -- A quotient's constants, or a constructor or recursor reached on its own: added as they are.
    return { names := #[b], consts := #[info.updateName? (r b) |>.getD info], note := some "not checked" }
where
  mkRecName (n : Name) : Name := n.str "rec"

/-- The expressions of a block that its mentions are read from: what is added, and what is
checked. -/
def Block.exprs (b : Block) : Array Expr :=
  b.consts.flatMap (fun c => #[c.type] ++ c.value?.toArray) ++
  match b.decl? with
  | some (.defnDecl d) => #[d.value]
  | some (.thmDecl t) => #[t.value]
  | some (.opaqueDecl o) => #[o.value]
  | _ => #[]

/-! ## The kernel's verdict -/

/-- The verdict on one declaration. -/
structure Verdict where
  /-- Constants the kernel needed that the closure lacks, in the order it asked for them. -/
  missing : Array Name := #[]
  /-- What the kernel said, if it failed for another reason than an unknown constant. -/
  error? : Option Kernel.Exception := none
  /-- Why it was not checked. -/
  skipped? : Option String := none

def Verdict.ok (v : Verdict) : Bool := v.missing.isEmpty && v.error?.isNone && v.skipped?.isNone

/-- Checks block `b` in `base` with the blocks `closure` added. -/
def checkBlock (base : Kernel.Environment) (blocks : Std.HashMap Name Block)
    (unren : Std.HashMap Name Name) (blockOfName : Std.HashMap Name Name) (heartbeats : Nat)
    (b : Name) (closure : Array Name) : Verdict := Id.run do
  let some blk := blocks.get? b | return { skipped? := some "not in the environment" }
  let some decl := blk.decl? | return { skipped? := blk.note.getD "not checked" }
  let add (env : Kernel.Environment) (c : Name) : Kernel.Environment :=
    if c == b then env else ((blocks.get? c).map (·.consts)).getD #[] |>.foldl kernelAdd env
  let mut env := closure.foldl add base
  let mut missing := #[]
  for _ in [0:64] do
    match env.addDeclCore heartbeats.toUSize 0 decl none with
    | .ok _ => return { missing }
    | .error (.unknownConstant _ n) =>
      let orig := unren.getD n n
      let ob := blockOfName.getD orig orig
      if ob == b || !blocks.contains ob || missing.contains orig then
        return { missing, error? := some (.other s!"unknown constant {orig}") }
      missing := missing.push orig
      env := add env ob
    | .error e => return { missing, error? := some e }
  return { missing, error? := some (.other "too many missing constants") }

/-- `s` with the renamed constants `_kc.<i>` given their names back. -/
def unrenameText (names : Array Name) (s : String) : String := Id.run do
  let parts := s.splitOn "_kc."
  let mut out := parts.headD ""
  for p in parts.drop 1 do
    let digits := p.toList.takeWhile Char.isDigit
    match (String.ofList digits).toNat? with
    | some i =>
      if h : i < names.size then
        out := out ++ names[i].toString ++ String.ofList (p.toList.drop digits.length)
      else out := out ++ "_kc." ++ p
    | none => out := out ++ "_kc." ++ p
  return out

/-! ## The check -/

/-- The result for one declaration: a row of the facet. -/
structure Row where
  decl : String
  /-- `ok`, `missing` (the closure lacks constants the kernel needed), `error` (the kernel
  rejected the declaration for another reason) or `skipped`. -/
  kernel : String
  missing : Array Name := #[]
  error : Option String := none
  /-- What the declaration mentions, through helpers, that its closure lacks. -/
  unlisted : Array Name := #[]

def Row.asJson (r : Row) : Json :=
  Json.mkObj <| [("decl", toJson r.decl), ("kernel", toJson r.kernel)] ++
    (if r.missing.isEmpty then [] else [("missing", toJson (r.missing.map (·.toString)))]) ++
    (match r.error with | some e => [("error", toJson e)] | none => []) ++
    (if r.unlisted.isEmpty then [] else [("unlisted", toJson (r.unlisted.map (·.toString)))])

def check (cfg : Config) : IO (Array Row) := do
  let t0 ← IO.monoMsNow
  unless cfg.notion == "meaning" || cfg.notion == "term" do
    throw <| IO.userError s!"--notion expects meaning or term, got `{cfg.notion}`"
  let g ← readGraph cfg.dataset cfg.notion cfg.dropEdges
  let mods ← if !cfg.modules.isEmpty then pure cfg.modules else do
    let mut ms := #[]
    for line in ← IO.FS.lines (cfg.dataset / "modules.jsonl") do
      if line.isEmpty then continue
      ms := ms.push ((← IO.ofExcept ((← IO.ofExcept (Json.parse line)).getObjValAs? String "name")).toName)
    pure ms
  initSearchPath (← findSysroot)
  progress t0 s!"importing {mods.size} modules"
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := true)
  progress t0 s!"imported {env.header.moduleNames.size} modules"

  -- The project's constants, in module order, and their new names.
  let mut projectConsts : Array Name := #[]
  for h : i in [0:env.header.moduleNames.size] do
    if cfg.root.isPrefixOf env.header.moduleNames[i] then
      projectConsts := projectConsts ++ env.header.moduleData[i]!.constNames
  let mut ren : Std.HashMap Name Name := {}
  let mut unren : Std.HashMap Name Name := {}
  let mut byString : Std.HashMap String Name := {}
  for h : i in [0:projectConsts.size] do
    let n := projectConsts[i]
    let n' := Name.mkNum `_kc i
    ren := ren.insert n n'
    unren := unren.insert n' n
    byString := byString.insert n.toString n
  let blockOfName : Std.HashMap Name Name :=
    projectConsts.foldl (init := {}) fun m n => m.insert n (blockOf env n)

  -- Blocks, built once. A block is a node if one of its constants is a node of the dataset.
  let erase? := cfg.notion == "meaning"
  let blockNames := (projectConsts.map (blockOfName.getD · .anonymous)).toList.eraseDups.toArray
  let (blocks, failures) ← runMetaM env do
    let mut blocks : Std.HashMap Name Block := {}
    let mut failures := 0
    for b in blockNames do
      let mut blk : Block := default
      try blk ← mkBlock ren erase? b
      catch e =>
        failures := failures + 1
        blk := { (← mkBlock ren false b) with note := some s!"not erased: {← e.toMessageData.toString}" }
      let acc ← IO.mkRef ({} : NameSet)
      for e in blk.exprs do mentioned e acc
      -- The expressions are renamed: read the project's constants back.
      let ms := (← acc.get).toArray.filterMap fun n =>
        (unren.get? n).bind fun o => (blockOfName.get? o).filter (· != b)
      blocks := blocks.insert b { blk with mentions := ms.toList.eraseDups.toArray }
    return (blocks, failures)
  progress t0 s!"{projectConsts.size} project constants in {blocks.size} blocks{if failures > 0 then s!", {failures} not erased" else ""}"

  let isNode (n : Name) : Bool := (g.ids.get? n.toString).any (g.project[·]!)
  let nodeBlocks : Std.HashSet Name := blocks.fold (init := {}) fun s b blk =>
    if blk.names.any isNode then s.insert b else s
  -- The base: the kernel environment as imported, and the project's helpers.
  let base := blocks.fold (init := env.toKernelEnv) fun kenv b blk =>
    if nodeBlocks.contains b then kenv else blk.consts.foldl kernelAdd kenv
  progress t0 s!"{nodeBlocks.size} blocks are nodes; the others ({blocks.size - nodeBlocks.size}) are helpers"

  -- What a helper mentions, through other helpers: the node blocks it reaches.
  let reach ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let rec throughHelpers (fuel : Nat) (b : Name) (onPath : Std.HashSet Name) : IO (Array Name) := do
    if let some r := (← reach.get).get? b then return r
    match fuel with
    | 0 => return #[]
    | fuel + 1 =>
      let mut out : Std.HashSet Name := {}
      for m in ((blocks.get? b).map (·.mentions)).getD #[] do
        if nodeBlocks.contains m then out := out.insert m
        else if !onPath.contains m then
          for x in ← throughHelpers fuel m (onPath.insert m) do out := out.insert x
      let r := out.toArray
      reach.modify (·.insert b r)
      return r

  -- The declarations to check: the dataset's project nodes of the imported project modules.
  let wanted : Std.HashSet String := cfg.decls.foldl (·.insert ·) {}
  let modSet : Std.HashSet String := mods.foldl (fun s m => s.insert m.toString) {}
  let mut todo : Array (Nat × Name) := #[]
  let mut absent := 0
  for h : i in [0:g.names.size] do
    if !g.project[i]! then continue
    if !wanted.isEmpty && !wanted.contains g.names[i] then continue
    if cfg.decls.isEmpty && !cfg.modules.isEmpty && !modSet.contains g.modules[i]! then continue
    match byString.get? g.names[i] with
    | some n => todo := todo.push (i, n)
    | none => absent := absent + 1
  if absent > 0 then
    IO.eprintln s!"warning: {absent} project nodes of the dataset are not in the environment: \
      is the project built at the dataset's commit?"

  -- Each declaration's closure, as blocks; and what it mentions that the closure lacks.
  let mut jobs : Array (Nat × Name × Array Name) := #[]
  let mut unlisted : Std.HashMap Nat (Array Name) := {}
  for (i, n) in todo do
    let b := blockOfName.getD n n
    let closure := (g.closure i).filterMap fun k =>
      if g.project[k]! then (byString.get? g.names[k]!).map (blockOfName.getD · .anonymous) else none
    let closureSet : Std.HashSet Name := closure.foldl (·.insert ·) {}
    let mut ment : Std.HashSet Name := {}
    for m in ((blocks.get? b).map (·.mentions)).getD #[] do
      if nodeBlocks.contains m then ment := ment.insert m
      else for x in ← throughHelpers 1000 m {m} do ment := ment.insert x
    let un := ment.toArray.filter fun m => m != b && !closureSet.contains m
    unlisted := unlisted.insert i (un.qsort (·.toString < ·.toString))
    jobs := jobs.push (i, b, closure.toList.eraseDups.toArray)
  progress t0 s!"checking {jobs.size} declarations along `{cfg.notion}`"

  let run (js : Array (Nat × Name × Array Name)) : Array (Nat × Verdict) :=
    js.map fun (i, b, closure) =>
      (i, checkBlock base blocks unren blockOfName (cfg.heartbeats * 1000) b closure)
  let n := max 1 cfg.jobs
  let chunk := (jobs.size + n - 1) / n
  let tasks := (List.range n).toArray.map fun k =>
    Task.spawn fun _ => run (jobs.extract (k * chunk) ((k + 1) * chunk))
  let verdicts := tasks.flatMap Task.get
  progress t0 "checked"
  verdicts.mapM fun (i, v) => do
    let error ← match v.error?, v.skipped? with
      | some e, _ => pure (some (unrenameText projectConsts (← (e.toMessageData {}).toString)))
      | none, some why => pure (some why)
      | none, none => pure none
    let kernel := if v.skipped?.isSome then "skipped" else if v.error?.isSome then "error"
      else if v.missing.isEmpty then "ok" else "missing"
    return { decl := g.names[i]!, kernel, missing := v.missing, error,
             unlisted := unlisted.getD i #[] : Row }
/-- The facet's name for a notion. -/
def facetName (notion : String) : String := s!"check.kernel.{notion}"

/-- Runs the check, prints a summary, and writes the facet into the dataset. Returns how many
declarations failed. -/
def run (cfg : Config) : IO Nat := do
  let rows ← check cfg
  let count (k : String) := (rows.filter (·.kernel == k)).size
  let missingConsts := (rows.flatMap (·.missing)).toList.eraseDups.length
  let unlisted := (rows.filter (!·.unlisted.isEmpty)).size
  IO.println s!"{rows.size} declarations checked along `{cfg.notion}`: {count "ok"} ok, \
    {count "missing"} with constants missing from their closure ({missingConsts} distinct), \
    {count "error"} rejected for another reason, {count "skipped"} skipped; \
    {unlisted} mention something their closure lacks"
  for r in rows do
    if r.kernel == "missing" then
      IO.println s!"  missing  {r.decl}: {", ".intercalate (r.missing.map toString).toList}"
    else if r.kernel == "error" then
      IO.println s!"  error    {r.decl}: {(r.error.getD "").replace "\n" " "}"
  for r in rows do
    if !r.unlisted.isEmpty then
      IO.println s!"  unlisted {r.decl}: {", ".intercalate (r.unlisted.map toString).toList}"
  if cfg.write && cfg.dropEdges.isEmpty then
    let name := facetName cfg.notion
    let file := s!"facets/{name}.jsonl"
    IO.FS.createDirAll (cfg.dataset / "facets")
    writeJsonl (cfg.dataset / file) (rows.map (·.asJson))
    let metaPath := cfg.dataset / "meta.json"
    let metaJson ← IO.ofExcept (Json.parse (← IO.FS.readFile metaPath))
    let facets := ((metaJson.getObjValAs? (Array Json) "facets").toOption.getD #[]).filter fun f =>
      (f.getObjValAs? String "name").toOption != some name
    let entry := Json.mkObj [("name", toJson name), ("file", toJson file),
      ("schema", toJson "check.kernel/1"), ("count", toJson rows.size),
      ("description", toJson s!"Lean's kernel checked each project declaration against its \
        `{cfg.notion}` closure only (proofs erased for `meaning`): `kernel` is ok, missing (with \
        the constants the kernel needed that the closure lacks), error or skipped; `unlisted` \
        names what the declaration mentions, through helpers, that its closure lacks")]
    IO.FS.writeFile metaPath ((metaJson.setObjVal! "facets" (Json.arr (facets.push entry))).pretty ++ "\n")
    IO.println s!"wrote {file}"
  return rows.size - count "ok"

end TrustExtractor.Check
