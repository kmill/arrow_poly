import ArrowPoly.ArrowPoly
import ArrowPoly.LoadKnot

def main : List String → IO Unit
| [fname] => do
  IO.println s!"loading {fname}"
  let knots ← parseFile fname
  IO.println s!"loaded {knots.size} knots"
  for (name, pd) in knots do
    IO.println s!"---\ncalculating for {name}"
    IO.println s!"{pd}"
    IO.println s!"writhe = {pd.writhe}"
    let pd' := pd.writhe_normalize
    IO.println s!"{pd'}"
    let p := arrow_poly pd'
    IO.println s!"{p}"
| _ =>
  throw <| IO.userError "Expecting exactly one argument"
