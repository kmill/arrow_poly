import ArrowPoly.Extra.ListExtra

inductive Node (α : Type _)
| Xp (a b c d : α)
| Xm (a b c d : α)
| P (a b : α)
deriving DecidableEq, Repr, Inhabited

/- Xp: Represents a right-handed oriented crossing like
       
  c ^ ^ b
     /
  d / \ a

  where a, b, c, and d are edge ids. -/

/- Xm: Represents a left-handed oriented crossing like
       
  d ^ ^ c
     \
  a / \ b

  where a, b, c, and d are edge ids. -/

def Node.ids : Node α → List α
| .Xp a b c d => [a, b, c, d]
| .Xm a b c d => [a, b, c, d]
| .P a b => [a, b]

def Node.writhe : Node α → Int
| .Xp _ _ _ _ => 1
| .Xm _ _ _ _ => -1
| .P _ _ => 0

local infixl:50 " ^^ " => Nat.max

def Node.max_id : Node Nat → Nat
| .Xp a b c d => a ^^ b ^^ c ^^ d
| .Xm a b c d => a ^^ b ^^ c ^^ d
| .P a b => a ^^ b

instance [ToString α] : ToString (Node α) where
  toString
  | .Xp a b c d => s!"Xp[{a},{b},{c},{d}]"
  | .Xm a b c d => s!"Xm[{a},{b},{c},{d}]"
  | .P a b => s!"P[{a},{b}]"

/-- Planar diagram

Each index should appear at most twice. -/
def PD α := Array (Node α)

def PD.is_valid [DecidableEq α] (pd : PD α) : Prop := ∀ x, pd.toList.count x ≤ 2

instance : Inhabited (PD α) := ⟨#[]⟩

/-- Give the number of crossings in the diagram. -/
def PD.crossings [Inhabited α] (pd : PD α) : Nat := Id.run do
  let mut c := 0
  for i in [:pd.size] do
    match pd[i] with
    | .Xp _ _ _ _ => c := c + 1
    | .Xm _ _ _ _ => c := c + 1
    | .P _ _ => pure ()
  return c

def PD.writhe (pd : PD α) : Int := pd.foldl (λ w node => w + node.writhe) 0

def PD.max_id (pd : PD Nat) : Nat := pd.foldl (λ w node => w ^^ node.max_id) 0

instance [Repr α] : Repr (PD α) where
  reprPrec pd := reprPrec (id pd : Array (Node α))

instance [ToString α] : ToString (PD α) where
  toString pd := "PD[" ++ ", ".intercalate (pd.map toString).toList ++ "]"

/-- Create a PD with zero writhe. The `bdry` is the `(low, high)` pair where
adding in a `P high low` completes the knot. -/
def PD.writhe_normalize (pd : PD Nat) (bdry : Nat × Nat) : PD Nat × Nat × Nat := Id.run do
  let mut pd := pd
  let mut i := bdry.2 -- high
  let wr := pd.writhe
  for j in [0 : wr.natAbs] do
    if wr > 0 then
      pd := pd.push <| .Xm i (i+1) (i+1) (i+2)
    else
      pd := pd.push <| .Xp (i+1) (i+1) (i+2) i
    i := i + 2
  return (pd, bdry.1, i)
