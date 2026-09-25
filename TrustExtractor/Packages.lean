import Lean

/-!
# Which package a module belongs to

A compiled module does not record its package. Under `lake env`, every package contributes one
directory to the search path, `<package>/.lake/build/lib/lean`, so the package of a module is read
off the directory its `.olean` is found in:

* under `…/.lake/packages/<name>/…`: the dependency `<name>`;
* under the Lean toolchain's own library: `lean4`;
* anywhere else: the project itself.
-/

namespace TrustExtractor

open Lean

/-- One search-path entry and the package it belongs to. -/
structure SearchEntry where
  dir : System.FilePath
  package : String

/-- The package label of a search-path directory. -/
def packageOfDir (sysroot : System.FilePath) (project : String) (dir : System.FilePath) : String :=
  let s := dir.toString
  let marker := "/.lake/packages/"
  match s.splitOn marker with
  | _ :: rest :: _ => (rest.splitOn "/").headD project
  | _ => if s.startsWith sysroot.toString then "lean4" else project

/-- The search path, labelled with packages. -/
def labelledSearchPath (project : String) : IO (Array SearchEntry) := do
  let sysroot ← findSysroot
  let sp ← searchPathRef.get
  return sp.toArray.map fun dir => { dir, package := packageOfDir sysroot project dir }

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
