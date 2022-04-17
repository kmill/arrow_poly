import ArrowPoly.Knot
import ArrowPoly.Extra.ArrayExtra
import ArrowPoly.Poly

/-- "arrow Temperley-Lieb path" -/
structure ATLP where
  (fst snd : Nat)
  whiskers : Int
  normalized : fst ≤ snd
deriving Repr, Ord

instance : ToString ATLP where
  toString p := s!"P[{p.fst},{p.snd},{p.whiskers}]"

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
  (- Poly.A 2 - Poly.A (-2)) * Poly.K (p.whiskers.natAbs / 2)

@[simp] theorem ATLP.loop_eval_nonzero (p : ATLP) (h : p.fst = p.snd) :
  p.loop_eval h ≠ 0 :=
sorry

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
  coeff : Poly
  paths : Array ATLP
  coeff_nonzero : coeff ≠ 0 := by simp [*]
  ordered : paths |>.map ATLP.toPair |>.strictIncreasing
  nodup : (paths.toList.bind ATLP.indices).nodup
deriving Repr

instance : ToString ATLD where
  toString d := toString d.coeff ++ " * D[" ++ ",".intercalate (d.paths.map toString).toList ++ "]"

def ATLD.one : ATLD where
  coeff := 1
  paths := #[]
  ordered := Array.strictIncreasing_empty
  nodup := List.nodup.nil

instance : Inhabited ATLD := ⟨ATLD.one⟩

instance : Coe ATLP ATLD where
  coe p :=
    if hp : p.fst = p.snd then
      { coeff := p.loop_eval hp
        paths := #[],
        ordered := Array.strictIncreasing_empty,
        nodup := List.nodup.nil }
    else
      { coeff := 1,
        paths := #[p],
        ordered := Array.strictIncreasing_singleton _,
        nodup := by
          show List.nodup [p.fst, p.snd]
          apply List.nodup.cons
          cases p
          intro h
          cases h
          · simp at hp
          · simp at hp
            rename_i h'
            cases h' }

local instance : LT (Array ATLP) := ltOfOrd

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

def ATLD.concat_path (paths : Array ATLP) (p : ATLP) (q : Poly) : Poly × Array ATLP :=
  if h : p.fst = p.snd then
    (q * p.loop_eval h, paths)
  else
    ATLD.concat_path_aux paths 0 p q

def ATLD.concat_aux (d d' : ATLD) : Poly × Array ATLP := Id.run do
  let mut q := d.coeff * d'.coeff
  let mut paths := d.paths
  for p in d'.paths do
    (q, paths) := ATLD.concat_path paths p q
  return (q, paths)

def ATLD.concat (d d' : ATLD) : ATLD :=
  let (q, paths) := ATLD.concat_aux d d'
  { coeff := q,
    paths := paths,
    coeff_nonzero := sorry,
    ordered := sorry,
    nodup := sorry }

def ATLD.ofArray (paths : Array ATLP) (q : Poly := 1) : ATLD := Id.run do
  let mut q : Poly := q
  let mut d : Array ATLP := #[]
  for p in paths do
    (q, d) := ATLD.concat_path d p q
  return { coeff := q,
           paths := d,
           coeff_nonzero := sorry,
           ordered := sorry,
           nodup := sorry }

def ATLD.scale (d : ATLD) (q : Poly) (hq : q ≠ 0) : ATLD where
  coeff := d.coeff * q
  paths := d.paths
  coeff_nonzero := sorry
  ordered := d.ordered
  nodup := d.nodup

structure ATL where
  diagrams : Array ATLD
  ordered : diagrams |>.map ATLD.paths |>.strictIncreasing
deriving Repr

instance : ToString ATL where
  toString a := "ATL[" ++ ", ".intercalate (a.diagrams.map toString).toList ++ "]"

def ATL.zero : ATL where
  diagrams := #[]
  ordered := Array.strictIncreasing_empty

def ATL.one : ATL where
  diagrams := #[ATLD.one]
  ordered := Array.strictIncreasing_singleton _

def ATL.add (x y : ATL) : ATL :=
  let f (p : Array ATLD) : Merge ATLD → Array ATLD
    | .left m₁ => p.push m₁
    | .right m₂ => p.push m₂
    | .both m₁ m₂ =>
      let q := m₁.coeff + m₂.coeff
      if h : q = 0 then
        p
      else
        p.push <| {m₁ with coeff := q, coeff_nonzero := h}
  let p := Array.mergeBy ATLD.paths f #[] x.diagrams y.diagrams
  have : (p.map ATLD.paths).strictIncreasing := by
    sorry
  ⟨p, this⟩

instance : Add ATL where
  add := ATL.add

def ATL.scale (x : ATL) (p : Poly) : ATL :=
  if hp : p = 0 then
    ATL.zero
  else
    { diagrams := x.diagrams.map (λ d => d.scale p hp),
      ordered := sorry }

def ATL.mulDiagram (x : ATL) (d : ATLD) : ATL := Id.run do
  let mut diagrams : Array ATLD := #[]
  for xd in x.diagrams do
    let d' := xd.concat d
    diagrams := Id.run <| diagrams.binInsertM' (λ (d1 d2 : ATLD) => d1.paths < d2.paths)
      (merge := fun d'' =>
        let c := d'.coeff + d''.coeff
        if hc : c = 0 then
          none
        else
          some { coeff := c,
                 paths := d''.paths,
                 ordered := d''.ordered,
                 nodup := d''.nodup })
      (add := fun _ => d')
      d'
  return { diagrams := diagrams,
           ordered := sorry }

def ATL.mul (x y : ATL) : ATL := Id.run do
  let mut z := ATL.zero
  for d in y.diagrams do
    z := z + x.mulDiagram d
  return z

instance : Mul ATL where
  mul := ATL.mul

instance : HMul Poly ATL ATL where
  hMul q t := t.scale q

instance : Coe ATLD ATL where
  coe d := { diagrams := #[d], ordered := Array.strictIncreasing_singleton _ }

def ATL.P (i j : Nat) (whiskers : Int := 0) : ATL := ATLP.mk' i j whiskers

def ATL.Xp (i j k l : Nat) : ATL :=
  ATLD.ofArray #[ATLP.mk' i j 0, ATLP.mk' l k 0] (Poly.A 1)
  + ATLD.ofArray #[ATLP.mk' i l 1, ATLP.mk' j k 1] (Poly.A (-1))

def ATL.Xm (i j k l : Nat) : ATL :=
  ATLD.ofArray #[ATLP.mk' j k 0, ATLP.mk' i l 0] (Poly.A (-1))
  + ATLD.ofArray #[ATLP.mk' j i 1, ATLP.mk' k l 1] (Poly.A 1)

def ATL.finalize (a : ATL) : Poly := Id.run do
  let mut p : Poly := 0
  for d in a.diagrams do
    if d.paths.size = 1 then
      p := p + d.coeff * Poly.K (d.paths[0].whiskers.natAbs / 2)
    else
      panic! "ATL.finalize: internal error"
  return p

def arrow_poly (p : PD Nat) : Poly := Id.run do
  let mut a : ATL := ATL.one
  for node in (id p : Array _) do
    let a' := match node with
              | .Xp a b c d => ATL.Xp a b c d
              | .Xm a b c d => ATL.Xm a b c d
              | .P a b => ATL.P a b
    a := a * a'
  return a.finalize

/-
#eval toString <| (2 : Poly) * ATL.one * ATL.one * (ATLP.mk' 1 2 0 : ATL) * (ATLP.mk' 1 2 0 : ATL)

#eval toString <| ATL.Xp 1 2 3 4

#eval toString <| ATL.finalize <| ATL.Xm 2 0 3 1 * ATL.Xm 3 1 4 2

#eval toString <| ATL.finalize <| ATL.Xm 2 5 1 4 * ATL.Xp 4 0 3 1 * ATL.Xp 6 2 5 3

#eval toString <| ATL.finalize <| ATL.Xp 8 4 7 5 * ATL.Xp 4 0 3 1 * ATL.Xp 2 6 1 7 * ATL.Xp 6 2 5 3
-/