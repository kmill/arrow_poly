import ArrowPoly.ArrowPoly

def main : List String → IO Unit
| [fname] =>
  IO.println s!"loading {fname}"
| _ =>
  throw <| IO.userError "Expecting exactly one argument"
