import ArrowPoly.Extra.ArrayExtra
import ArrowPoly.Extra.IntExtra

attribute [local instance] Array.lexicographic

local instance : LT (Array Int) := ltOfOrd

structure Monomial where
  exponents : Array Int
  coeff : Int
  coeff_nonzero : coeff ≠ 0 := by simp [*]
  exp_norm : exponents.back? ≠ some 0 := by simp [*]
  deriving Repr, Ord

instance : DecidableEq Monomial :=
λ m1 m2 =>
  if h : m1.coeff = m2.coeff ∧ m1.exponents = m2.exponents then
    isTrue (by { cases m1; cases m2; simp [h.1, h.2] })
  else
    isFalse (by { intro h; cases h; simp at h })

/-- compact Mathematica-compatible representation -/
instance : ToString Monomial where
  toString m :=
    toString m.coeff ++ "*M[" ++ ",".intercalate (m.exponents.map toString).toList ++ "]"

instance : Inhabited Monomial := ⟨{ exponents := #[], coeff := 1 }⟩

structure Poly where
  terms : Array Monomial
  incr : (terms.map Monomial.exponents).strictIncreasing
  deriving Repr, Ord

instance : DecidableEq Poly :=
λ p1 p2 =>
  if h : p1.terms = p2.terms then
    isTrue (by { cases p1; cases p2; cases h; simp })
  else
    isFalse (by { intro h; cases h; simp at h })

/-- compact Mathematica-compatible representation -/
instance : ToString Poly where
  toString p := "Poly[" ++ ", ".intercalate (p.terms.map toString).toList ++ "]"

@[inline]
def Poly.zero : Poly where
  terms := #[]
  incr := by intros i; cases i.isLt

instance : Inhabited Poly := ⟨Poly.zero⟩

def Poly.zero? (p : Poly) : Bool := p.terms.size = 0

theorem Poly.zero?_iff (p : Poly) : p.zero? ↔ p = Poly.zero := by
  cases p with | mk terms =>
  cases terms with | mk as =>
  unfold zero?
  unfold zero
  simp [Array.size, List.length_eq_zero_iff]

@[inline]
def Monomial.incl (n : Int) (hn : n ≠ 0 := by simp) : Monomial where
  coeff := n
  exponents := #[]

@[inline]
def Monomial.scale (m : Monomial) (n : Int) (hn : n ≠ 0) : Monomial where
  coeff := n * m.coeff
  exponents := m.exponents
  coeff_nonzero := by
    intro h
    cases Int.eq_zero_or_eq_zero_of_mul_eq_zero _ _ h
    · apply hn; assumption
    · apply m.coeff_nonzero; assumption
  exp_norm := m.exp_norm

@[inline]
def Monomial.mul (m₁ m₂ : Monomial) : Monomial where
  coeff := m₁.coeff * m₂.coeff
  exponents := (Array.zipWith' m₁.exponents m₂.exponents (. + .)).popZeros
  coeff_nonzero := by
    intro h
    cases Int.eq_zero_or_eq_zero_of_mul_eq_zero _ _ h
    · apply m₁.coeff_nonzero; assumption
    · apply m₂.coeff_nonzero; assumption
  exp_norm := Array.back?_popZeros _

def Poly.add (p₁ p₂ : Poly) : Poly :=
  let f (p : Array Monomial) : Merge Monomial → Array Monomial
    | .left m₁ => p.push m₁
    | .right m₂ => p.push m₂
    | .both m₁ m₂ =>
      if h : m₁.coeff + m₂.coeff = 0 then
        p
      else
        p.push <| {m₁ with coeff := m₁.coeff + m₂.coeff, coeff_nonzero := h}
  let p := Array.mergeBy Monomial.exponents f (Array.mkEmpty <| p₁.terms.size + p₂.terms.size)
            p₁.terms p₂.terms
  have : (p.map Monomial.exponents).strictIncreasing := by
    sorry
  ⟨p, this⟩

instance : Add Poly where
  add := Poly.add

def Poly.sub (p₁ p₂ : Poly) : Poly :=
  let f (p : Array Monomial) : Merge Monomial → Array Monomial
    | .left m₁ => p.push m₁ 
    | .right m₂ => p.push {m₂ with coeff := -m₂.coeff, coeff_nonzero := by simp [m₂.coeff_nonzero]}
    | .both m₁ m₂ =>
      if h : m₁.coeff - m₂.coeff = 0 then
        p
      else
        p.push <| {m₁ with coeff := m₁.coeff - m₂.coeff, coeff_nonzero := h}
  let p := Array.mergeBy Monomial.exponents f (Array.mkEmpty <| p₁.terms.size + p₂.terms.size)
            p₁.terms p₂.terms
  have : (p.map Monomial.exponents).strictIncreasing := by
    sorry
  ⟨p, this⟩

instance : Sub Poly where
  sub := Poly.sub

def Poly.mulScalar (p : Poly) (c : Int) (hc : c ≠ 0) : Poly where
  terms := p.terms.map (λ m => m.scale c hc)
  incr := by
    intro i j hij
    cases i with | mk i hi =>
    cases j with | mk j hj =>
    rw [Array.get_map, Array.get_map, Array.get_map, Array.get_map]
    · have := p.incr ⟨i, by { simp at hi; simp [hi] }⟩ ⟨j, by { simp at hj; simp [hj] }⟩
      simp at this
      specialize this hij
      rw [Array.get_map, Array.get_map] at this
      · simp [Monomial.scale, this]
      · simp at hj
        exact hj
      · simp at hi
        exact hi
    all_goals
      simp at hi hj
      simp [hi, hj]

instance : HMul Int Poly Poly where
  hMul c p :=
    if h : c = 0
    then Poly.zero
    else if c = 1
    then p
    else p.mulScalar c h

instance : Neg Poly where
  neg p := (-1 : Int) * p

def Poly.mulMonomial (p : Poly) (m : Monomial) : Poly :=
  if m.exponents.size = 0 then
    m.coeff * p
  else
    { terms := p.terms.map m.mul,
      incr := sorry }

def Poly.mul (p₁ p₂ : Poly) : Poly := Id.run do
  -- it's generally better to iterate over the shorter polynomial
  let (p₁, p₂) := if p₁.terms.size ≥ p₂.terms.size then (p₁, p₂) else (p₂, p₁)
  let mut q : Poly := Poly.zero
  for m₂ in p₂.terms do
    q := q + p₁.mulMonomial m₂
  return q

instance : Mul Poly where
  mul := Poly.mul

instance : Coe Monomial Poly where
  coe m :=
    { terms := #[m],
      incr := by
        intros i j hij
        cases i with | mk i hi =>
        cases j with | mk j hj =>
        have hi : i < 1 := hi
        have hj : j < 1 := hj
        simp at hi hj
        cases hi
        cases hj
        cases hij }

instance : Pow Poly Nat where
  pow :=
    let rec aux : Poly → Nat → Poly
      | p, 0 => Monomial.incl 1
      | p, (n+1) => aux p n * p
    aux

instance : Coe Int Poly where
  coe n := if h : n = 0 then Poly.zero else Monomial.incl n h

instance : OfNat Poly n where
  ofNat := (n : Int)

def Poly.one_ne_zero : (1 : Poly) ≠ (0 : Poly) := by simp

def Poly.toList (p : Poly) : List (Int × List Int) := Id.run do
  let mut q := []
  for m in p.terms do
    q := q.concat (m.coeff, m.exponents.toList)
  return q

def Poly.fromList (terms : List (Int × List Int)) : Poly := Id.run do
  let mut p := Poly.zero
  for (c, exp) in terms do
    let m : Monomial := { coeff := 1, exponents := exp.toArray.popZeros,
                          exp_norm := Array.back?_popZeros _ }
    p := p + c * m
  return p

@[inline]
def Poly.A (exp : Int := 1) : Poly :=
  if he : exp = 0 then Monomial.incl 1
  else { coeff := 1, exponents := #[exp],
         exp_norm := by { show some exp ≠ some 0; simp [he] } : Monomial }

@[inline]
def Poly.K (i : Nat) (exp : Nat := 1) : Poly :=
  if he : exp = 0 then Monomial.incl 1
  else if hi : i = 0 then Monomial.incl 1
  else {coeff := 1, exponents := (Array.mkArray i 0).push exp : Monomial }

/-- Negate the exponent of the "A" variable. -/
def Monomial.mirror (m : Monomial) : Monomial where
  coeff := m.coeff
  exponents :=
    if m.exponents.isEmpty then
      m.exponents
    else
      m.exponents.set! 0 (-m.exponents[0])
  coeff_nonzero := m.coeff_nonzero
  exp_norm := by
    split
    · rename_i h
      rw [Array.eq_empty_of_isEmpty h]
      simp
    · have := m.exp_norm
      sorry

/-- Negate the exponent of the "A" variable. Corresponds to taking the mirror image of
the knot. -/
def Poly.mirror (p : Poly) : Poly :=
  p.terms.foldl (λ q term => q + term.mirror) 0

/-- Eliminate all K variables, setting them to one. -/
def Monomial.subst_K_one (m : Monomial) : Monomial where
  coeff := m.coeff
  exponents := (m.exponents.shrink 1).popZeros
  coeff_nonzero := m.coeff_nonzero
  exp_norm := Array.back?_popZeros _

/-- Eliminate all K variables, setting them to one.
(Used to convert from arrow polynomial to Kauffman bracket) -/
def Poly.subst_K_one (p : Poly) : Poly :=
p.terms.foldl (λ q m => q + m.subst_K_one) 0
