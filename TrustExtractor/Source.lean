import Lean
import TrustExtractor.Util

/-!
# Where a declaration is written, and with which keyword

The keyword (`theorem` or `lemma`, `def` or `abbrev`, …) is editorial intent that the compiled
environment does not keep: Lean records `theorem` and `lemma` as the same kind. It is read from the
source text at the start of the declaration's range, past its docstring, attributes and modifiers.
Adapted from Referee's `collect` (LeanMachineLearning/exposition).
-/

namespace TrustExtractor

open Lean

/-- Modifiers Lean allows between a declaration's attributes and its keyword. -/
def declModifiers : Array String :=
  #["private", "protected", "public", "noncomputable", "unsafe", "partial", "nonrec", "scoped",
    "local", "meta"]

/-- The relative path of a module's source file, e.g. `TauCeti/Foo/Bar.lean`. -/
def modulePath (mod : Name) : System.FilePath :=
  System.mkFilePath (mod.components.map toString) |>.addExtension "lean"

/-- The source file of `mod`: the first of `srcDirs` containing it. -/
def findSource? (srcDirs : Array System.FilePath) (mod : Name) : IO (Option System.FilePath) := do
  for dir in srcDirs do
    let p := dir / modulePath mod
    if ← p.pathExists then return some p
  return none

/-- The keyword a declaration is written with, read from `text` starting at character offset
`start`: skips whitespace, comments (including the docstring), attributes `@[…]` and modifiers.
`class inductive` is returned as one keyword. -/
partial def keywordAt (text : String) (start : String.Pos.Raw) : Option String :=
  go (start.byteIdx) 0
where
  at? (i : Nat) : Option Char :=
    if i < text.utf8ByteSize then some (String.Pos.Raw.get text ⟨i⟩) else none
  next (i : Nat) : Nat := i + ((at? i).map Char.utf8Size |>.getD 1)
  startsWith (i : Nat) (s : String) : Bool :=
    (String.Pos.Raw.extract text ⟨i⟩ ⟨i + s.utf8ByteSize⟩) == s
  /-- Skips a block comment starting at `i` (at its opening delimiter), honouring nesting. -/
  skipBlock (i : Nat) (depth : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => text.utf8ByteSize
    | fuel + 1 =>
      if i ≥ text.utf8ByteSize then i
      else if startsWith i "/-" then skipBlock (i + 2) (depth + 1) fuel
      else if startsWith i "-/" then
        if depth ≤ 1 then i + 2 else skipBlock (i + 2) (depth - 1) fuel
      else skipBlock (next i) depth fuel
  skipLine (i : Nat) : Nat :=
    match at? i with
    | none => i
    | some '\n' => i + 1
    | some _ => skipLine (next i)
  /-- Skips `@[ … ]`, starting at `i` (at `@`), balancing brackets. -/
  skipAttr (i : Nat) (depth : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => text.utf8ByteSize
    | fuel + 1 =>
      match at? i with
      | none => i
      | some '[' => skipAttr (i + 1) (depth + 1) fuel
      | some ']' => if depth ≤ 1 then i + 1 else skipAttr (i + 1) (depth - 1) fuel
      | some _ => skipAttr (next i) depth fuel
  word (i : Nat) (acc : String) : String × Nat :=
    match at? i with
    | some c =>
      if c.isAlphanum || c == '_' then word (next i) (acc.push c) else (acc, i)
    | none => (acc, i)
  go (i : Nat) (fuel : Nat) : Option String :=
    if fuel > 10000 then none else
    match at? i with
    | none => none
    | some c =>
      if c.isWhitespace then go (next i) (fuel + 1)
      else if startsWith i "/-" then go (skipBlock i 0 1000000) (fuel + 1)
      else if startsWith i "--" then go (skipLine i) (fuel + 1)
      else if startsWith i "@[" then go (skipAttr (i + 1) 0 1000000) (fuel + 1)
      else
        let (w, j) := word i ""
        if w.isEmpty then none
        else if declModifiers.contains w then go j (fuel + 1)
        else if w == "class" then
          -- `class inductive`
          let rest := go j (fuel + 1)
          if rest == some "inductive" then some "class inductive" else some "class"
        else some w

/-- Where a declaration is written. Lines are 1-based and columns 0-based, as in Lean's
`DeclarationRanges`. -/
structure SourceLoc where
  path : String
  startLine : Nat
  startCol : Nat
  endLine : Nat
  endCol : Nat
  keyword : Option String

def SourceLoc.asJson (decl : Name) (s : SourceLoc) : Json :=
  Json.mkObj <|
    [("decl", toJson decl.toString), ("path", toJson s.path),
     ("start", toJson #[s.startLine, s.startCol]), ("end", toJson #[s.endLine, s.endCol])] ++
    (match s.keyword with | some k => [("keyword", toJson k)] | none => [])

end TrustExtractor
