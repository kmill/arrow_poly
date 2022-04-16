import ArrowPoly.Knot
import ArrowPoly.ArrayExtra
import Lean.Data.Parsec
import Std.Data.AssocList

/-! # Loading knots from Gauss codes

This is for loading Gauss codes in the format seen in Jeremy Green's table of virtual knots.
https://www.math.toronto.edu/drorbn/Students/GreenJ/results.html

-/

/-- i.e., right-handed and left-handed crossings -/
inductive CrossingType | Pos | Neg
  deriving Repr, DecidableEq, Inhabited

inductive Passing | Over | Under
  deriving Repr, DecidableEq, Inhabited

/-- This is one of the entries in a Gauss code. There are two of these entries per crossing. -/
structure GaussEntry (α : Type _) where
  label : α
  crossing_type : CrossingType
  passing : Passing
  deriving Repr, DecidableEq, Inhabited

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

/-- The knots-6 file has symmetries at the start of each line. We just skip them. -/
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

/--
Create a PD from the parsed Gauss code. Note: rather than producing a knot, this gives
a tangle. A reason for this is that the Jones/arrow polynomials are normalized such that
the unknot evaluates to 1, and a way to implement that is to cut the knot open into a
tangle -- so we may as well not close it up in the first place!
-/
def processGaussCode [Inhabited α] [DecidableEq α]
  (code : Array (GaussEntry α)) : Option (PD Nat) := Id.run
do
  if code.isEmpty then
    return some #[Node.P 0 1]
  let mut other_idx : Array Nat := .mkArray code.size 0
  let mut label_idxs : Std.AssocList α Nat := .empty
  let mut complete_labels : Array α := #[]
  for (i, e) in code.enumerate do
    match label_idxs.find? e.label with
    | none =>
      label_idxs := label_idxs.insert e.label i
    | some j =>
      if complete_labels.contains e.label then
        -- saw the label three times
        return none
      other_idx := other_idx |>.set! i j |>.set! j i
      complete_labels := complete_labels.push e.label
  for e in code do
    if ¬ complete_labels.contains e.label then
      -- saw the label only once
      return none
  -- Now label_idxs records for each GaussEntry the index of the other entry with the same label

  let mut pd : PD Nat := #[]

  for i in [0 : code.size] do
    let j := other_idx[i]
    if i < j then
      let entryi := code[i]
      let entryj := code[j]
      match entryi.passing, entryi.crossing_type, entryj.passing, entryj.crossing_type with
      | .Over, .Pos, .Under, .Pos => pd := pd.push <| Node.Xp j (i+1) (j+1) i
      | .Under, .Pos, .Over, .Pos => pd := pd.push <| Node.Xp i (j+1) (i+1) j
      | .Over, .Neg, .Under, .Neg => pd := pd.push <| Node.Xm j i (j+1) (i+1)
      | .Under, .Neg, .Over, .Neg => pd := pd.push <| Node.Xm i j (i+1) (j+1)
      | _, _, _, _ => return none -- Invalid combination

  return pd

--#eval parseLineOfString "idhv O1-O2-U1-O3+U2-O4-U3+U4-"
--#eval parseLineOfString "O1-O2-U1-O3+U2-O4-U3+U4-"

def parseFile (fname : System.FilePath) : IO (Array (String × PD Nat)) := do
  let mut line := 1
  let mut crossings := 0
  let mut idx := 1
  let mut knots : Array (String × PD Nat) := #[]
  for s in ← IO.FS.lines fname do
    if s.startsWith "Number" then
      -- The end of each knot file ends in a summary
      break
    match parseLineOfString s with
    | .error msg => throw $ IO.userError s!"{line}:{msg}"
    | .ok code => do
      let some pd := processGaussCode code | throw (IO.userError "Invalid Gauss code")
      if pd.crossings ≠ crossings then
        crossings := pd.crossings
        idx := 1
      let name := s!"{crossings}_{idx}"
      knots := knots |>.push (name, pd)
      idx := idx + 1
    line := line + 1
  return knots
