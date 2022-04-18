import ArrowPoly.ArrowPoly
import ArrowPoly.LoadKnot

structure knot_data where
  name : String
  polys : Array Poly
  polys' : Array Poly

attribute [local instance] Array.lexicographic
local instance [Inhabited α] [Ord α] : LT (Array α) := ltOfOrd
local instance : LT Poly := ltOfOrd

def calculate_knot (cache : ATLCache) (name : String) (pd : PD Nat) (bdry : Nat × Nat) :
  ATLCache × knot_data :=
Id.run do
  let mut cache := cache
  let (pd, bdry) := pd.writhe_normalize bdry
  let mut polys : Array Poly := #[]
  for n in [1:4] do
    let (cache', p) := cache.cabled_arrow_poly n pd bdry
    polys := polys.push p
    cache := cache'
  let mut polys' := polys.map Poly.mirror
  if polys' < polys then
    (polys, polys') := (polys', polys)
  return (cache, { name := name, polys := polys, polys' := polys' })

def main : List String → IO Unit
| [fname] => do
  IO.println s!"loading {fname}"
  let knots ← parseFile fname
  IO.println s!"loaded {knots.size} knots"
  let mut cache := ATLCache.empty
  for (name, pd, bdry) in knots do
    IO.println s!"---\ncalculating for {name}"
    --let (cache', data) := calculate_knot cache name pd bdry
    --cache := cache'
    IO.println s!"{pd}"
    IO.println s!"boundary = {bdry}"
    IO.println s!"writhe = {pd.writhe}"
    let (pd, bdry) := pd.writhe_normalize bdry
    IO.println s!"{pd}"
    IO.println s!"boundary = {bdry}"
    for n in [1:4] do
      let (cache', p) := cache.cabled_arrow_poly n pd bdry
      cache := cache'
      IO.println s!"{n} => {p}"
| _ =>
  throw <| IO.userError "Expecting exactly one argument"
