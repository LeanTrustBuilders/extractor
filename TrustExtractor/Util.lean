import Lean

/-!
# Small utilities shared by the extractor
-/

namespace TrustExtractor

open Lean

/-- A 64-bit hash as 16 lowercase hexadecimal digits. -/
def hex16 (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- Appends `n` as a little-endian 32-bit integer. -/
def pushI32LE (buf : ByteArray) (n : Nat) : ByteArray :=
  let v := n.toUInt32
  buf.push (v &&& 0xff).toUInt8
    |>.push ((v >>> 8) &&& 0xff).toUInt8
    |>.push ((v >>> 16) &&& 0xff).toUInt8
    |>.push ((v >>> 24) &&& 0xff).toUInt8

/-- Runs a `MetaM` action against an already-imported environment. -/
def runMetaM (env : Environment) (x : MetaM α) : IO α := do
  let ctx : Core.Context :=
    { fileName := "<trust-extract>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8000 }
  let ((a, _), _) ← (x.run {} {}).toIO ctx { env := env }
  return a

/-- Runs a `CoreM` action against an already-imported environment. -/
def runCoreM (env : Environment) (x : CoreM α) : IO α := do
  let ctx : Core.Context :=
    { fileName := "<trust-extract>", fileMap := default, maxHeartbeats := 0, maxRecDepth := 8000 }
  let (a, _) ← x.toIO ctx { env := env }
  return a

/-- Progress on stderr, with the time elapsed since `start` (from `IO.monoMsNow`). -/
def progress (start : Nat) (msg : String) : IO Unit := do
  let ms := (← IO.monoMsNow) - start
  IO.eprintln s!"[{ms / 1000}.{(ms % 1000) / 100}s] {msg}"

/-- Writes one JSON value per line. -/
def writeJsonl (path : System.FilePath) (values : Array Json) : IO Unit := do
  let h ← IO.FS.Handle.mk path .write
  for v in values do
    h.putStrLn v.compress

/-- The output of a command, trimmed, or `none` if it failed. -/
def commandOutput? (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    IO (Option String) := do
  try
    let out ← IO.Process.output { cmd, args, cwd }
    if out.exitCode == 0 then return some out.stdout.trimAscii.toString else return none
  catch _ => return none

end TrustExtractor
