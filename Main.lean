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
  --check-deps         check the dependencies against MeaningGraph's own computation (slow)
  --no-axioms          skip the axioms facet

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
  | "--no-term" :: rest => parseOpts rest { cfg with term := false } extra
  | "--check-deps" :: rest => parseOpts rest { cfg with checkDeps := true } extra
  | "--jobs" :: v :: rest =>
    match v.toNat? with
    | some n => parseOpts rest { cfg with jobs := n } extra
    | none => .error s!"--jobs expects a number, got `{v}`"
  | "--modules-file" :: v :: rest => parseOpts rest cfg (("modules-file", v) :: extra)
  | "--part-out" :: v :: rest => parseOpts rest cfg (("part-out", v) :: extra)
  | a :: _ => .error s!"unknown argument `{a}`"

unsafe def main (args : List String) : IO UInt32 := do
  -- Imported modules' `initialize` declarations must run, so that their environment extensions
  -- (in particular `TrustAnnotations`') are registered and receive their imported entries.
  enableInitializersExecution
  match args with
  | "extract" :: rest =>
    match parseOpts rest { root := .anonymous } [] with
    | .error e => IO.eprintln s!"{e}\n\n{usage}"; return 2
    | .ok (cfg, _) =>
      if cfg.root.isAnonymous then
        IO.eprintln s!"--root is required\n\n{usage}"; return 2
      try
        extract cfg
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
      semantic_hash {semanticHashRevision}, local hash {localHasherName}, Lean {Lean.versionString}"
    return 0
  | _ => IO.eprintln usage; return 2
