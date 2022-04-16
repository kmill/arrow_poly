import ArrowPoly.ArrowPoly
import ArrowPoly.LoadKnot

def main : List String → IO Unit
| [fname] => do
  IO.println s!"loading {fname}"
  let knots ← parseFile fname
  IO.println s!"loaded {knots.size} knots"
| _ =>
  throw <| IO.userError "Expecting exactly one argument"
