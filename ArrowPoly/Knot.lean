import ArrowPoly.ListExtra

inductive Node (α : Type _)
| Xp (a b c d : α)
| Xm (a b c d : α)
| P (a b : α)
deriving DecidableEq, Repr

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
def PD α := List (Node α)

def PD.is_valid [DecidableEq α] (pd : PD α) : Prop := ∀ x, pd.count x ≤ 2
