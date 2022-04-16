import ArrowPoly.ListExtra

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

/-- Planar diagram

Each index should appear at most twice. -/
def PD α := Array (Node α)

def PD.is_valid [DecidableEq α] (pd : PD α) : Prop := ∀ x, pd.toList.count x ≤ 2

/-- Give the number of crossings in the diagram. -/
def PD.crossings [Inhabited α] (pd : PD α) : Nat := Id.run do
  let mut c := 0
  for i in [:pd.size] do
    match pd[i] with
    | .Xp _ _ _ _ => c := c + 1
    | .Xm _ _ _ _ => c := c + 1
    | .P _ _ => pure ()
  return c

instance [Repr α] : Repr (PD α) where
  reprPrec pd := reprPrec (id pd : Array (Node α))
