import ArrowPoly.Knot
import ArrowPoly.Extra.ArrayExtra
import ArrowPoly.Poly

/-- "arrow Temperley-Lieb path" -/
structure ATLP where
  (fst snd : Nat)
  whiskers : Int
  normalized : fst ≤ snd
deriving Repr, Ord

instance : Inhabited ATLP := ⟨{ fst := 0, snd := 0, whiskers := 0, normalized := Nat.le.refl }⟩

local instance : LT ATLP := ltOfOrd

def ATLP.mk' (fst snd : Nat) (whiskers : Int) : ATLP :=
  if h : fst ≤ snd then
    { fst := fst, snd := snd, whiskers := whiskers, normalized := h }
  else
    { fst := snd, snd := fst, whiskers := -whiskers, normalized := by
        rw [Nat.not_le] at h
        exact Nat.le_of_lt h }

def ATLP.toPair (p : ATLP) : Nat × Nat := (p.fst, p.snd)
def ATLP.indices (p : ATLP) : List Nat := [p.fst, p.snd]

def ATLP.loop_eval (p : ATLP) (h : p.fst = p.snd) : Poly :=
  (- Poly.A 2 - Poly.A (-2)) * Poly.K p.whiskers.natAbs

def ATLP.combine (p1 p2 : ATLP) : Option ATLP :=
  if p1.fst = p2.fst then
    ATLP.mk' p1.snd p2.snd (-p1.whiskers + p2.whiskers)
  else if p1.fst = p2.snd then
    ATLP.mk' p1.snd p2.fst (-p1.whiskers - p2.whiskers)
  else if p1.snd = p2.fst then
    ATLP.mk' p1.fst p2.snd (p1.whiskers + p2.whiskers)
  else if p1.snd = p2.snd then
    ATLP.mk' p1.fst p2.fst (p1.whiskers - p2.whiskers)
  else none

attribute [local instance] Array.lexicographic

/-- "arrow Templerley-Lieb diagram" -/
structure ATLD where
  paths : Array ATLP
  ordered : paths |>.map ATLP.toPair |>.strictIncreasing
  nodup : (paths.toList.bind ATLP.indices).nodup
deriving Repr, Ord

instance : Inhabited ATLD :=
  ⟨{ paths := #[], ordered := Array.strictIncreasing_empty, nodup := List.nodup.nil }⟩

local instance : LT ATLD := ltOfOrd

def ATLD.concat_path_aux (paths : Array ATLP) (i : Nat) (p : ATLP) (q : Poly) : Poly × Array ATLP :=
  if hi : i < paths.size then
    match ATLP.combine paths[i] p with
    | none => concat_path_aux paths (i + 1) p q
    | some p' =>
      let paths' := paths.eraseIdx' ⟨i, hi⟩
      if h : p'.fst = p'.snd then
        (q * p'.loop_eval h, paths')
      else
        have : Array.size (Array.eraseIdx' paths { val := i, isLt := hi }).val - i
                < Array.size paths - i := by
          simp [(Array.eraseIdx' paths { val := i, isLt := hi }).property]
          generalize hn : Array.size paths = n
          rw [hn] at hi
          rw [Nat.sub_sub, Nat.add_comm]
          exact Nat.sub_succ_lt_self _ _ hi
        concat_path_aux paths' i p' q
  else
    (q, paths.binInsert (· < ·) p)
termination_by _ => paths.size - i

def ATLD.concat_path (d : ATLD) (p : ATLP) (q : Poly := 1) : Poly × ATLD :=
  if h : p.fst = p.snd then
    (q * p.loop_eval h, d)
  else
    let (q', paths') := ATLD.concat_path_aux d.paths 0 p q
    (q', { paths := paths',
           ordered := sorry, nodup := sorry })

def ATLD.concat (d d' : ATLD) (q : Poly := 1) : Poly × ATLD := Id.run do
  let mut q := q
  let mut d := d
  for p in d'.paths do
    (q, d) := d.concat_path p q
  return (q, d)


/-- Create an ATLD by sorting the input array. -/
def ATLD.ofArray (paths : Array ATLP) : Poly × ATLD := Id.run do
  let mut q : Poly := 1
  let mut d : ATLD := default
  for p in paths do
    (q, d) := d.concat_path p q
  return (q, d)

structure ATL where
  diagrams : Array (ATLD × Poly)
  ordered : diagrams |>.map Prod.fst |>.strictIncreasing