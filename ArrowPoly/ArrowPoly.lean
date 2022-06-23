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

/-- "arrow Temperley-Lieb diagram" -/
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
  match h : ATLD.concat_aux d d' with
  | (c, p) =>
    { coeff := c
      paths := p,
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

@[inline]
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

@[inline]
def ATL.zero : ATL where
  diagrams := #[]
  ordered := Array.strictIncreasing_empty

@[inline]
def ATL.one : ATL where
  diagrams := #[ATLD.one]
  ordered := Array.strictIncreasing_singleton _

instance : Inhabited ATL := ⟨ATL.one⟩

def ATL.add (x y : ATL) : ATL :=
  let f (p : Array ATLD) : Merge ATLD → Array ATLD
    | .left m₁ => p.push m₁
    | .right m₂ => p.push m₂
    | .both m₁ m₂ =>
      let q := m₁.coeff + m₂.coeff
      if h : q.zero? then
        p
      else
        p.push <| {m₁ with coeff := q, coeff_nonzero := by { simp [Poly.zero?_iff] at h; exact h } }
  let p := Array.mergeBy ATLD.paths f #[] x.diagrams y.diagrams
  have : (p.map ATLD.paths).strictIncreasing := by
    sorry
  ⟨p, this⟩

instance : Add ATL where
  add := ATL.add

def ATL.scale (x : ATL) (p : Poly) : ATL :=
  if hp : p.zero? then
    ATL.zero
  else
    { diagrams := x.diagrams.map (λ d => d.scale p (by { simp [Poly.zero?_iff] at hp; exact hp })),
      ordered := sorry }

def ATL.mulDiagram (x : ATL) (d : ATLD) : ATL := Id.run do
  let mut diagrams : Array ATLD := #[]
  for xd in x.diagrams do
    let d' := xd.concat d
    diagrams := Id.run <| diagrams.binInsertM' (λ (d1 d2 : ATLD) => d1.paths < d2.paths)
      (merge := fun d'' =>
        let c := d'.coeff + d''.coeff
        if hc : c.zero? then
          none
        else
          some { coeff := c,
                 coeff_nonzero := by { simp [Poly.zero?_iff] at hc; exact hc },
                 paths := d''.paths,
                 ordered := d''.ordered,
                 nodup := d''.nodup })
      (add := fun _ => d')
      d'
  return { diagrams := diagrams,
           ordered := sorry }

def ATL.mul (x y : ATL) : ATL := Id.run do
  -- it's generally better to iterate over the ATL with fewer terms
  let (x, y) := if x.diagrams.size ≥ y.diagrams.size then (x, y) else (y, x)
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

/-! ## PD nodes as ATL elements -/

def ATL.P (i j : Nat) (whiskers : Int := 0) : ATL := ATLP.mk' i j whiskers

def ATL.Xp (i j k l : Nat) : ATL :=
  ATLD.ofArray #[ATLP.mk' i j 0, ATLP.mk' l k 0] (Poly.A 1)
  + ATLD.ofArray #[ATLP.mk' i l 1, ATLP.mk' j k 1] (Poly.A (-1))

def ATL.Xm (i j k l : Nat) : ATL :=
  ATLD.ofArray #[ATLP.mk' j k 0, ATLP.mk' i l 0] (Poly.A (-1))
  + ATLD.ofArray #[ATLP.mk' j i 1, ATLP.mk' k l 1] (Poly.A 1)

/-! ## Relabeling -/

def ATLP.relabel (f : Nat → Nat) (p : ATLP) : ATLP :=
  ATLP.mk' (f p.fst) (f p.snd) p.whiskers

def ATLD.relabel (f : Nat → Nat) (d : ATLD) : ATLD :=
  ATLD.ofArray (d.paths.map (ATLP.relabel f)) d.coeff

def ATL.relabel (f : Nat → Nat) (a : ATL) : ATL :=
  a.diagrams.foldl (λ b d => b + d.relabel f) ATL.zero

/-! ## Converting PD's to ATL's and computing the arrow polynomial -/

def Node.toATL : Node Nat → ATL
| .Xp a b c d => ATL.Xp a b c d
| .Xm a b c d => ATL.Xm a b c d
| .P a b => ATL.P a b

/-- Convert a `PD` to an `ATL` using the arrow polynomial skein relation. -/
def PD.toATL (pd : PD Nat) : ATL :=
  pd.foldl (λ a node => a * node.toATL) ATL.one

/-- Numbers indices such that, with respect to orientation of an arc, are
  in this order:

  ^ ^ ^ ^
  | | | |
  | | | |
  0 1 2 3

  The boundary ends up using `4 * n` indices. While this uses internal indices,
  the intent is that this be converted to an `ATL` so that they disappear and
  only the boundary indices remain.

 -/
def PD.cabled_Xp (n : Nat) : PD Nat := Id.run do
  let mut pd : PD Nat := #[]
  for i in [0 : n] do
    for j in [0 : n] do
      let a := if i + 1 = n then j else 4*n+n*(n-2) - n*i + j
      let b := if j + 1 = n then n + i else 4*n+n*(n-1) + n*j + i
      let c := if i = 0 then 2*n + j else 4*n+n*(n-2) - n*(i-1) + j
      let d := if j = 0 then 3*n + i else 4*n+n*(n-1) + n*(j-1) + i
      pd := pd.push <| Node.Xp a b c d
  return pd

/-- Same convention as for `PD.cabled_Xp` -/
def PD.cabled_Xm (n : Nat) : PD Nat := Id.run do
  let mut pd : PD Nat := #[]
  for i in [0 : n] do
    for j in [0 : n] do
      let a := if j = 0 then i else 4*n + i + n*(j-1)
      let b := if i + 1 = n then n + j else 4*n+n*(2*n-3) - n*i + j
      let c := if j + 1 = n then 2*n + i else 4*n + i + n*j
      let d := if i = 0 then 3*n + j else 4*n+n*(2*n-3) - n*(i-1) + j
      pd := pd.push <| Node.Xm a b c d
  return pd

def PD.cabled_P (n : Nat) : PD Nat := Id.run do
  let mut pd : PD Nat := #[]
  for i in [0 : n] do
    pd := pd.push <| Node.P i (n + i)
  return pd

--#eval toString <| PD.cabled_Xp 3
--#eval toString <| PD.cabled_Xm 3
--#eval toString <| PD.cabled_P 3

def ATL.cabled_Xp (n : Nat) : ATL := (PD.cabled_Xp n).toATL

def ATL.cabled_Xm (n : Nat) : ATL := (PD.cabled_Xm n).toATL

def ATL.cabled_P (n : Nat) (a b : Nat) : ATL := Id.run do
  let mut x : ATL := ATL.one
  for i in [0 : n] do
    x := x * ATLP.mk' (n*a + i) (n*b + i) 0
  return x

--#eval toString <| ATL.cabled_Xp 2
--#eval (ATL.cabled_Xp 4).diagrams.size -- 1252

structure ATLCache where
  cached_xp : Array ATL
  cached_xm : Array ATL
  cached_pos_twist : Array (Array ATL)
  cached_neg_twist : Array (Array ATL)
deriving Repr

def ATLCache.empty : ATLCache where
  cached_xp := #[]
  cached_xm := #[]
  cached_pos_twist := #[]
  cached_neg_twist := #[]

/-- Given an `ATL.cabled_Xp n` or `ATL.cabled_Xm n`, relabel it.

The indices are all multiplied by `n` to make space for all the intermediate indices. -/
def ATL.cabled_crossing_relabel (x : ATL) (n : Nat) (a b c d : Nat) : ATL :=
  x.relabel <| λ i =>
    if i < n then n*a + i
    else if i < 2*n then n*b + i - n
    else if i < 3*n then n*c + i - 2*n
    else n*d + i - 3*n

def ATL.path_relabel (x : ATL) (n : Nat) (a b : Nat) : ATL :=
  x.relabel <| λ i =>
    if i < n then n*a + i
    else n*b + i - n

def ATLCache.ensure_xp (cache : ATLCache) (n : Nat) : ATLCache := Id.run do
  let mut cache := cache
  for n' in [cache.cached_xp.size : n + 1] do
    cache := { cache with cached_xp := cache.cached_xp.push (ATL.cabled_Xp n') }
  return cache

def ATLCache.ensure_xm (cache : ATLCache) (n : Nat) : ATLCache := Id.run do
  let mut cache := cache
  for n' in [cache.cached_xm.size : n + 1] do
    cache := { cache with cached_xm := cache.cached_xm.push (ATL.cabled_Xm n') }
  return cache

def ATLCache.ensure_pos_twist (cache : ATLCache) (n : Nat) (wr : Nat) : ATLCache := Id.run do
  let cache := cache.ensure_xp n
  let mut pcache := cache.cached_pos_twist
  for n' in [pcache.size : n + 1] do
    pcache := pcache.push #[ATL.cabled_P n' 0 1,
                            cache.cached_xp[n'].cabled_crossing_relabel n' 2 2 1 0]
  let mut pcachen := pcache[n]
  for wr' in [pcachen.size : wr + 1] do
    let a1 := pcachen[wr'-1].path_relabel n 0 2
    let a2 := pcachen[1].path_relabel n 2 1
    pcachen := pcachen.push <| a1 * a2
  return { cache with cached_pos_twist := pcache.set! n pcachen }

def ATLCache.ensure_neg_twist (cache : ATLCache) (n : Nat) (wr : Nat) : ATLCache := Id.run do
  let cache := cache.ensure_xm n
  let mut mcache := cache.cached_neg_twist
  for n' in [mcache.size : n + 1] do
    mcache := mcache.push #[ATL.cabled_P n' 0 1,
                            cache.cached_xm[n'].cabled_crossing_relabel n' 0 2 2 1]
  let mut mcachen := mcache[n]
  for wr' in [mcachen.size : wr + 1] do
    let a1 := mcachen[wr'-1].path_relabel n 0 2
    let a2 := mcachen[1].path_relabel n 2 1
    mcachen := mcachen.push <| a1 * a2
  return { cache with cached_neg_twist := mcache.set! n mcachen }

--#eval ATLCache.empty.ensure_pos_twist 1 4

/--
Create cabled positive crossing using indices.

The indices are all multiplied by `4 * n` to make space for all the intermediate indices.
-/
def ATLCache.Xp (cache : ATLCache) (n : Nat) (a b c d : Nat) : ATLCache × ATL :=
  let cache := cache.ensure_xp n
  let x := cache.cached_xp[n].cabled_crossing_relabel n a b c d
  (cache, x)

def ATLCache.Xm (cache : ATLCache) (n : Nat) (a b c d : Nat) : ATLCache × ATL :=
  let cache := cache.ensure_xm n
  let x := cache.cached_xm[n].cabled_crossing_relabel n a b c d
  (cache, x)

def ATLCache.twist (cache : ATLCache) (n : Nat) (wr : Int) (a b : Nat) : ATLCache × ATL :=
  if wr ≥ 0 then
    let cache := cache.ensure_pos_twist n wr.natAbs
    let y := cache.cached_pos_twist[n][wr.natAbs].path_relabel n a b
    (cache, y)
  else
    let cache := cache.ensure_neg_twist n wr.natAbs
    let y := cache.cached_neg_twist[n][wr.natAbs].path_relabel n a b
    (cache, y)

--#eval toString <| (ATLCache.empty.twist 3 (6) 0 1).2

def ATLCache.ofNode (cache : ATLCache) (n : Nat) : Node Nat → ATLCache × ATL
| .Xp a b c d => cache.Xp n a b c d
| .Xm a b c d => cache.Xm n a b c d
| .P a b => (cache, ATL.cabled_P n a b)

--#eval toString <| (ATLCache.empty.Xm 2 10 20 30 40).2

/--
We are calculating arrow polynomials of 1-strand tangles, so this is the step where we finally
close them up. If we were to close things up before this point, then the polynomial would be
multiplied by (-A^2 - A^-2), and we're using the standard that the unknot has arrow polynomial 1.
-/
def ATL.finalize (a : ATL) : Poly := Id.run do
  let mut p : Poly := 0
  for d in a.diagrams do
    if d.paths.size = 1 then
      p := p + d.coeff * Poly.K (d.paths[0].whiskers.natAbs / 2)
    else
      p := panic! "ATL.finalize: internal error"
  return p

/-- Calculate the arrow polynomial. -/
def arrow_poly (p : PD Nat) : Poly :=
  p.toATL.finalize

/-- Calculate the cabled arrow polynomial. Generalizes `arrow_poly`. -/
def ATLCache.cabled_arrow_poly (cache : ATLCache) (n : Nat) (pd : PD Nat) (bdry : Nat × Nat) :
  ATLCache × Poly := Id.run
do
  let mut cache := cache
  let mut a : ATL := ATL.one
  let pd := pd.plan bdry.1
  --let (pd, bdry) := pd.writhe_normalize bdry
  --let j := bdry.2
  let j := pd.max_id + 1
  -- Connect all but one back up
  for i in [1 : n] do
    a := a * ATLP.mk' (n*j + i) (n*bdry.1 + i) 0
  -- Process nodes
  for node in (id pd : Array _) do
    let (cache', node') := cache.ofNode n node
    cache := cache'
    a := a * node'
  let (cache', wr_node) := cache.twist n (-pd.writhe) bdry.2 j
  cache := cache'
  a := a * wr_node
  return (cache, a.finalize)

--#eval ATLCache.empty.cabled_arrow_poly

/-
#eval toString <| (2 : Poly) * ATL.one * ATL.one * (ATLP.mk' 1 2 0 : ATL) * (ATLP.mk' 1 2 0 : ATL)

#eval toString <| ATL.Xp 1 2 3 4

#eval toString <| ATL.finalize <| ATL.Xm 2 0 3 1 * ATL.Xm 3 1 4 2

#eval toString <| ATL.finalize <| ATL.Xm 2 5 1 4 * ATL.Xp 4 0 3 1 * ATL.Xp 6 2 5 3

#eval toString <| ATL.finalize <| ATL.Xp 8 4 7 5 * ATL.Xp 4 0 3 1 * ATL.Xp 2 6 1 7 * ATL.Xp 6 2 5 3
-/

--#eval toString <| Prod.snd <|
--  ATLCache.empty.cabled_arrow_poly 3 #[Node.Xp 0 4 1 3, Node.Xp 4 2 5 1, Node.Xp 2 6 3 5] (0, 6)