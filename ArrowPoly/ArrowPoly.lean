import ArrowPoly.Knot
import ArrowPoly.ArrayExtra

/-- "arrow Temperley-Lieb path" -/
structure ATLP where
  (fst snd : Nat)
  whiskers : Int
  normalized : fst ≤ snd
deriving Repr, Ord

def ATLP.mk' (fst snd : Nat) (whiskers : Int := 0) : ATLP :=
  if h : fst ≤ snd then
    { fst := fst, snd := snd, whiskers := whiskers, normalized := h }
  else
    { fst := snd, snd := fst, whiskers := -whiskers, normalized := by
        rw [Nat.not_le] at h
        exact Nat.le_of_lt h }

local instance : LT ATLP := ltOfOrd

/-- "arrow Templerley-Lieb diagram" -/
structure ATLD where
  paths : Array ATLP
  normalized : paths.strictIncreasing

/-- Create an ATLD by sorting the input array. -/
def ATLD.ofArray (a : Array ATLP) : ATLD where
  paths := a.insertionSort (· < ·)
  normalized := sorry