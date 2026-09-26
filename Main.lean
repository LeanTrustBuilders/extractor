import TrustExtractor

open Lean TrustExtractor

def usage : String := "\
trust-extract: extract an S2 dataset (ltb-dataset/0) from a compiled Lean project.

Run inside the project, under `lake env`:

  lake env trust-extract extract --root <Prefix> [options]
  trust-extract version

Options for `extract`:
  --root <Prefix>      root module prefix of the project (required), e.g. TauCeti
  --out <dir>          output directory (default: dataset)
  --src-dir <dir>      where the project's sources are (repeatable; default: .)
  --module <Module>    import this module instead of discovering them (repeatable)
  --repo <owner/name>  the project's repository, recorded in meta.json
  --commit <sha>       the project's commit (default: git rev-parse HEAD)
  --package <name>     the project's package label (default: the root prefix)
  --parts <n>          split the work into n parts from the start (default: 1). A part that
                       cannot import its modules, typically because the process runs out of
                       memory mappings (vm.max_map_count), is split in two and retried
  --jobs <n>           run up to n parts at once (default: 1)
  --no-term            skip the `term` notion, which walks every proof term
  --no-axioms          skip the axioms facet
  --no-statements      skip the statement facet (each statement taken apart and pretty-printed)
  --no-refs            in the statement facet, do not record which constant each identifier names
  --no-signatures      skip the signature facet (every node's signature, for hovers)
  --no-upstream-docs   give docstrings for the project's declarations only
  --upstream-closure <statement|meaning|term>
                       follow dependencies past the project along this notion (`term`: what a
                       definition's value mentions, the lemmas its proofs call included, as trust
                       draws it). Every upstream declaration reached becomes a node, with edges of
                       its own in `upstream-<notion>` files; the statement facet covers the ones
                       that are not proofs
  --skip-module <Module>
                       do not extract this module, typically because it does not build at this
                       commit; every module importing it is skipped too (repeatable). The
                       dataset lists the skipped modules in meta.json (`library.unavailable`)
  --skip-modules-file <file>
                       the same, one module per line, e.g. the failures Lake reports:
                         lake build --no-build 2>&1 | sed -n '/logged failures/,$s/^- //p'

Check 2 of the suite's self-checks: Lean's kernel checks each project declaration against its
closure as a dataset records it, and names what the closure lacks:

  lake env trust-extract check --root <Prefix> --dataset <dir> [options]
  --notion <meaning|term>  the closures to check (default: meaning, proofs erased)
  --module <Module>        import this module and check its declarations (repeatable; default:
                           the dataset's modules)
  --decl <Name>            check this declaration only (repeatable)
  --jobs <n>               run n checks at once (default: 1)
  --heartbeats <n>         the kernel's limit per declaration, in thousands (default: none)
  --drop-edge <A> <B>      leave out the edge from A to B, to test the check (writes nothing)
  --no-write               do not write the facet check.kernel.<notion> into the dataset
  --strict                 exit with 1 if a declaration fails

Diagnostics:
  lake env trust-extract diagnose-import <private|server|exported> <Prefix | Module...>
"

partial def parseOpts (args : List String) (cfg : Config) (extra : List (String × String)) :
    Except String (Config × List (String × String)) :=
  match args with
  | [] => .ok (cfg, extra)
  | "--root" :: v :: rest => parseOpts rest { cfg with root := v.toName } extra
  | "--out" :: v :: rest => parseOpts rest { cfg with out := v } extra
  | "--src-dir" :: v :: rest =>
    let dirs := if cfg.srcDirs == #[("." : System.FilePath)] then #[] else cfg.srcDirs
    parseOpts rest { cfg with srcDirs := dirs.push (v : System.FilePath) } extra
  | "--module" :: v :: rest => parseOpts rest { cfg with modules := cfg.modules.push v.toName } extra
  | "--repo" :: v :: rest => parseOpts rest { cfg with repo := v } extra
  | "--commit" :: v :: rest => parseOpts rest { cfg with commit := v } extra
  | "--package" :: v :: rest => parseOpts rest { cfg with project := v } extra
  | "--parts" :: v :: rest =>
    match v.toNat? with
    | some n => parseOpts rest { cfg with parts := n } extra
    | none => .error s!"--parts expects a number, got `{v}`"
  | "--no-axioms" :: rest => parseOpts rest { cfg with axioms := false } extra
  | "--no-statements" :: rest => parseOpts rest { cfg with statements := false } extra
  | "--no-refs" :: rest => parseOpts rest { cfg with refs := false } extra
  | "--no-signatures" :: rest => parseOpts rest { cfg with signatures := false } extra
  | "--no-upstream-docs" :: rest => parseOpts rest { cfg with upstreamDocs := false } extra
  | "--no-term" :: rest => parseOpts rest { cfg with term := false } extra
  | "--upstream-closure" :: v :: rest =>
    match followOfName? v with
    | some f => parseOpts rest { cfg with upstreamClosure := some f } extra
    | none => .error s!"--upstream-closure expects statement, meaning or term, got `{v}`"
  | "--jobs" :: v :: rest =>
    match v.toNat? with
    | some n => parseOpts rest { cfg with jobs := n } extra
    | none => .error s!"--jobs expects a number, got `{v}`"
  | "--skip-module" :: v :: rest => parseOpts rest { cfg with skip := cfg.skip.push v.toName } extra
  | "--skip-modules-file" :: v :: rest => parseOpts rest cfg (("skip-modules-file", v) :: extra)
  | "--modules-file" :: v :: rest => parseOpts rest cfg (("modules-file", v) :: extra)
  | "--part-out" :: v :: rest => parseOpts rest cfg (("part-out", v) :: extra)
  | a :: _ => .error s!"unknown argument `{a}`"

partial def parseCheck (args : List String) (cfg : Check.Config) (strict : Bool) :
    Except String (Check.Config × Bool) :=
  match args with
  | [] => .ok (cfg, strict)
  | "--root" :: v :: rest => parseCheck rest { cfg with root := v.toName } strict
  | "--dataset" :: v :: rest => parseCheck rest { cfg with dataset := v } strict
  | "--notion" :: v :: rest => parseCheck rest { cfg with notion := v } strict
  | "--module" :: v :: rest => parseCheck rest { cfg with modules := cfg.modules.push v.toName } strict
  | "--decl" :: v :: rest => parseCheck rest { cfg with decls := cfg.decls.push v } strict
  | "--drop-edge" :: a :: b :: rest => parseCheck rest { cfg with dropEdges := cfg.dropEdges.push (a, b) } strict
  | "--no-write" :: rest => parseCheck rest { cfg with write := false } strict
  | "--strict" :: rest => parseCheck rest cfg true
  | "--jobs" :: v :: rest =>
    match v.toNat? with
    | some n => parseCheck rest { cfg with jobs := n } strict
    | none => .error s!"--jobs expects a number, got `{v}`"
  | "--heartbeats" :: v :: rest =>
    match v.toNat? with
    | some n => parseCheck rest { cfg with heartbeats := n } strict
    | none => .error s!"--heartbeats expects a number, got `{v}`"
  | a :: _ => .error s!"unknown argument `{a}`"

unsafe def main (args : List String) : IO UInt32 := do
  -- Imported modules' `initialize` declarations must run, so that their environment extensions
  -- (in particular `TrustAnnotations`') are registered and receive their imported entries.
  enableInitializersExecution
  match args with
  | "extract" :: rest =>
    match parseOpts rest { root := .anonymous } [] with
    | .error e => IO.eprintln s!"{e}\n\n{usage}"; return 2
    | .ok (cfg, extra) =>
      if cfg.root.isAnonymous then
        IO.eprintln s!"--root is required\n\n{usage}"; return 2
      try
        let listed ← match extra.lookup "skip-modules-file" with
          | some f => pure (((← IO.FS.readFile f).splitOn "\n").map (·.trimAscii.toString)
              |>.filter (!·.isEmpty) |>.map (·.toName) |>.toArray)
          | none => pure #[]
        extract { cfg with skip := cfg.skip ++ listed }
        return 0
      catch e =>
        IO.eprintln s!"error: {e}"; return 1
  | "extract-part" :: rest =>
    -- Internal: one part of an extraction, run in a child process by `extract`.
    match parseOpts rest { root := .anonymous } [] with
    | .error e => IO.eprintln e; return 2
    | .ok (cfg, extra) =>
      let some modsFile := extra.lookup "modules-file" | IO.eprintln "--modules-file"; return 2
      let some out := extra.lookup "part-out" | IO.eprintln "--part-out"; return 2
      let mods := ((← IO.FS.readFile modsFile).splitOn "\n").filter (!·.isEmpty) |>.map (·.toName)
      try extractPart cfg mods.toArray out catch e =>
        IO.eprintln s!"error: {e}"; return 1
  | "check" :: rest =>
    match parseCheck rest { root := .anonymous } false with
    | .error e => IO.eprintln s!"{e}\n\n{usage}"; return 2
    | .ok (cfg, strict) =>
      if cfg.root.isAnonymous then
        IO.eprintln s!"--root is required\n\n{usage}"; return 2
      try
        let failed ← Check.run cfg
        return if strict && failed > 0 then 1 else 0
      catch e =>
        IO.eprintln s!"error: {e}"; return 1
  | "diagnose-import" :: level :: rest =>
    -- How many memory mappings importing costs, for `vm.max_map_count` problems. With a single
    -- prefix, imports every module under it.
    initSearchPath (← findSysroot)
    let lvl := match level with
      | "private" => OLeanLevel.private | "server" => .server | _ => .exported
    let mods ← match rest with
      | [root] => discoverModules #["."] root.toName
      | _ => pure (rest.toArray.map (·.toName))
    let count : IO Nat := return ((← IO.FS.readFile "/proc/self/maps").splitOn "\n").length
    let before ← count
    try
      let env ← importModules (mods.map ({ module := · })) {} (loadExts := true) (level := lvl)
      IO.println s!"{level}: {env.header.moduleNames.size} modules, mappings {before} → {← count}"
      return 0
    catch e =>
      IO.println s!"{level}: failed after {(← count) - before} new mappings: {e}"
      return 1
  | ["version"] =>
    IO.println s!"trust-extract {extractorVersion}, dataset spec {datasetSpec}, \
      meaning hash {MeaningGraph.Hash.Rule.meaning.name}, local hash {localHasherName}, \
      content hash semantic_hash {semanticHashRevision}, Lean {Lean.versionString}"
    return 0
  | _ => IO.eprintln usage; return 2
