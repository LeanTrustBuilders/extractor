import Lean

/-!
# Which package a module belongs to

A compiled module does not record its package. Under `lake env`, every package contributes one
directory to the search path, `<package>/.lake/build/lib/lean`, so the package of a module is read
off the directory its `.olean` is found in. The packages and their directories come from the
workspace's Lake manifest (`lake-manifest.json`, in the directory the extractor runs in), with
symbolic links resolved on both sides, so that a dependency linked in from elsewhere is still itself:

* in a dependency's directory: that dependency, by the name its lakefile declares (the deepest
  such directory, since a dependency can sit inside another's);
* under the Lean toolchain's own library: `lean4`;
* anywhere else: the project itself.

A package is labelled by its Lake name whether it is the project or a dependency (S1), so the
project's label is the root package's name in the manifest, not its root module prefix: Mathlib's
declarations are `mathlib` in Mathlib's own dataset as in any dataset downstream of it.
-/

namespace TrustExtractor

open Lean

/-- The packages of the workspace the extractor runs in, from its Lake manifest. -/
structure Workspace where
  /-- The root package's name, as its lakefile declares it; empty without a manifest. -/
  root : String := ""
  /-- Each dependency's name and directory, symbolic links resolved. -/
  packages : Array (String × System.FilePath) := #[]

/-- `p` with its symbolic links resolved, or `p` itself if it cannot be (it does not exist). -/
def realPathOrSelf (p : System.FilePath) : IO System.FilePath := do
  try IO.FS.realPath p catch _ => pure p

/-- The workspace in the current directory, from `lake-manifest.json`; empty without one. -/
def readWorkspace : IO Workspace := do
  let file : System.FilePath := "lake-manifest.json"
  unless ← file.pathExists do return {}
  let .ok j := Json.parse (← IO.FS.readFile file) | return {}
  let packagesDir := (j.getObjValAs? String "packagesDir").toOption.getD ".lake/packages"
  let mut packages := #[]
  for p in (j.getObjValAs? (Array Json) "packages").toOption.getD #[] do
    let .ok name := p.getObjValAs? String "name" | continue
    -- A path dependency names its directory; any other lives in the packages directory.
    let dir : System.FilePath := match p.getObjValAs? String "type", p.getObjValAs? String "dir" with
      | .ok "path", .ok d => d
      | _, _ => System.FilePath.mk packagesDir / name
    packages := packages.push (name, ← realPathOrSelf dir)
  return { root := (j.getObjValAs? String "name").toOption.getD "", packages }

/-- The project's package label: `label` (`--package`) if any, else the root package's name in the
workspace's manifest, else the root module prefix. -/
def projectLabel (label : String) (root : Name) : IO String := do
  if !label.isEmpty then return label
  let ws ← readWorkspace
  return if ws.root.isEmpty then root.toString else ws.root

/-- One search-path entry and the package it belongs to. -/
structure SearchEntry where
  dir : System.FilePath
  package : String

/-- The package label of a search-path directory. -/
def packageOfDir (sysroot : System.FilePath) (ws : Workspace) (project : String)
    (dir : System.FilePath) : IO String := do
  let d := (← realPathOrSelf dir).toString
  let under (p : System.FilePath) := d == p.toString || d.startsWith (p.toString ++ "/")
  let mut best : Option (String × Nat) := none
  for (name, p) in ws.packages do
    if under p && best.all (·.2 < p.toString.length) then best := some (name, p.toString.length)
  if let some (name, _) := best then return name
  if under (← realPathOrSelf sysroot) then return "lean4"
  -- Not in the manifest: a directory under `.lake/packages/<name>/` is still that package.
  match dir.toString.splitOn "/.lake/packages/" with
  | _ :: rest :: _ => return (rest.splitOn "/").headD project
  | _ => return project

/-- The search path, labelled with packages. -/
def labelledSearchPath (project : String) : IO (Array SearchEntry) := do
  let sysroot ← findSysroot
  let ws ← readWorkspace
  let sp ← searchPathRef.get
  sp.toArray.mapM fun dir => return { dir, package := ← packageOfDir sysroot ws project dir }

/-- The package of `mod`, memoized in `cache`. -/
def packageOf (entries : Array SearchEntry) (cache : IO.Ref (Std.HashMap Name String)) (mod : Name) :
    IO String := do
  if let some p := (← cache.get).get? mod then return p
  let rel := System.mkFilePath (mod.components.map toString) |>.addExtension "olean"
  let mut found := "unknown"
  for e in entries do
    if ← (e.dir / rel).pathExists then
      found := e.package
      break
  cache.modify (·.insert mod found)
  return found

end TrustExtractor
