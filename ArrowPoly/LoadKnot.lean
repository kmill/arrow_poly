import ArrowPoly.Knot
import Lean.Data.Parsec

/-! # Loading knots from Gauss codes

This is for loading Gauss codes in the format seen in Jeremy Green's table of virtual knots.
https://www.math.toronto.edu/drorbn/Students/GreenJ/results.html

-/

/-- i.e., right-handed and left-handed crossings -/
inductive CrossingType | Pos | Neg
  deriving Repr, DecidableEq

inductive Passing | Over | Under
  deriving Repr, DecidableEq

structure GaussEntry (α : Type _) where
  label : α
  crossing_type : CrossingType
  passing : Passing
  deriving Repr, DecidableEq

open Lean (Parsec)
open Lean.Parsec

def parseCrossingType : Parsec CrossingType :=
  pchar '+' *> pure CrossingType.Pos
  <|> pchar '-' *> pure CrossingType.Neg
  <|> fail "Expecting '+' or '-'"

def parsePassing : Parsec Passing :=
  pchar 'O' *> pure Passing.Over
  <|> pchar 'U' *> pure Passing.Under
  <|> fail "Expecting 'O' or 'U'"

def parseNatLabel : Parsec Nat := do
  let mut n : Nat := 0
  for c in ← many1 (satisfy Char.isDigit) do
    n := 10 * n + (c.toNat - '0'.toNat)
  return n

def parseGaussEntry : Parsec (GaussEntry Nat) := do
  let p ← parsePassing
  let n ← parseNatLabel
  let t ← parseCrossingType
  return { label := n, crossing_type := t, passing := p }

def parseGaussEntries : Parsec (Array (GaussEntry Nat)) :=
  many parseGaussEntry

/- the knots-6 file has symmetries at the start of each line -/
def parseSymmetries : Parsec Unit := attempt do
  skipChar '-' <|> skipChar 'i' <|> fail "Expecting '-' or 'i'"
  skipChar '-' <|> skipChar 'd' <|> fail "Expecting '-' or 'd'"
  skipChar '-' <|> skipChar 'h' <|> fail "Expecting '-' or 'h'"
  skipChar '-' <|> skipChar 'v' <|> fail "Expecting '-' or 'v'"

def parseLine : Parsec (Array (GaussEntry Nat)) := do
  parseSymmetries <|> pure ()
  ws
  parseGaussEntries <* ws <* (eof <|> fail "Expecting end of line")

def parseLineOfString (s : String) : Except String (Array (GaussEntry Nat)) :=
  match parseLine s.mkIterator with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error it err  => Except.error s!"{it.i}: {err}"

#eval parseLineOfString "idhv O1-O2-U1-O3+U2-O4-U3+U4-"
#eval parseLineOfString "O1-O2-U1-O3+U2-O4-U3+U4-"

def parseFile (fname : System.FilePath) : IO Unit := do
  let mut line := 1
  let mut crossings := 0
  let mut idx := 1
  for s in ← IO.FS.lines fname do
    match parseLineOfString s with
    | .error msg => throw $ IO.userError s!"{line}:{msg}"
    | .ok a => do
      if a.size ≠ crossings then
        crossings := a.size
        idx := 1
      let name := s!"{crossings}_{idx}"
      IO.println s!"{name}"
      idx := idx + 1
    line := line + 1
    if line > 10 then
      throw $ IO.userError "that's enough"
  return ()
