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
  --no-axioms          skip the axioms facet
"

partial def parseExtract (args : List String) (cfg : Config) : Except String Config :=
  match args with
  | [] => .ok cfg
  | "--root" :: v :: rest => parseExtract rest { cfg with root := v.toName }
  | "--out" :: v :: rest => parseExtract rest { cfg with out := v }
  | "--src-dir" :: v :: rest =>
    let dirs := if cfg.srcDirs == #[("." : System.FilePath)] then #[] else cfg.srcDirs
    parseExtract rest { cfg with srcDirs := dirs.push (v : System.FilePath) }
  | "--module" :: v :: rest => parseExtract rest { cfg with modules := cfg.modules.push v.toName }
  | "--repo" :: v :: rest => parseExtract rest { cfg with repo := v }
  | "--commit" :: v :: rest => parseExtract rest { cfg with commit := v }
  | "--package" :: v :: rest => parseExtract rest { cfg with project := v }
  | "--no-axioms" :: rest => parseExtract rest { cfg with axioms := false }
  | a :: _ => .error s!"unknown argument `{a}`"

unsafe def main (args : List String) : IO UInt32 := do
  -- Imported modules' `initialize` declarations must run, so that their environment extensions
  -- (in particular `TrustAnnotations`') are registered and receive their imported entries.
  enableInitializersExecution
  match args with
  | "extract" :: rest =>
    match parseExtract rest { root := .anonymous } with
    | .error e => IO.eprintln s!"{e}\n\n{usage}"; return 2
    | .ok cfg =>
      if cfg.root.isAnonymous then
        IO.eprintln s!"--root is required\n\n{usage}"; return 2
      try
        extract cfg
        return 0
      catch e =>
        IO.eprintln s!"error: {e}"; return 1
  | ["version"] =>
    IO.println s!"trust-extract {extractorVersion}, dataset spec {datasetSpec}, \
      semantic_hash {semanticHashRevision}, local hash {localHasherName}, Lean {Lean.versionString}"
    return 0
  | _ => IO.eprintln usage; return 2
