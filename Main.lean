import ArrowPoly.ArrowPoly
import ArrowPoly.LoadKnot

structure knot_data where
  name : String
  num : Nat
  polys : Array Poly
  polys' : Array Poly

attribute [local instance] Array.lexicographic
local instance [Inhabited α] [Ord α] : LT (Array α) := ltOfOrd
local instance : LT Poly := ltOfOrd

def calculate_knot (cache : ATLCache) (num : Nat) (name : String) (pd : PD Nat) (bdry : Nat × Nat) :
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
  return (cache, { name := name, num := num, polys := polys, polys' := polys' })

def knot_task (data : Array (String × PD Nat × Nat × Nat))
  (max_crossings : Nat)
  (nthreads : Nat) (thread : Nat) :
  IO (Array knot_data) :=
do
  let mut res : Array knot_data := #[]
  let mut cache := ATLCache.empty
  for i in [thread : data.size : nthreads] do
    let (name, pd, bdry) := data[i]
    if pd.crossings > max_crossings then break
    let (cache', knot) := calculate_knot cache i name pd bdry
    IO.println s!"calculated for {knot.name}"
    res := res.push knot
  return res

def main : List String → IO Unit
| [fname] => do
  IO.println s!"loading {fname}"
  let knots ← parseFile fname
  IO.println s!"loaded {knots.size} knots"
  let nthreads := 12
  let max_crossings := 5
  let mut tasks := #[]
  for thread in [0 : nthreads] do
    tasks := tasks.push (← IO.asTask (knot_task knots max_crossings nthreads thread))
  let mut res := #[]
  for t in tasks do
    let res' ← IO.ofExcept (← IO.wait t)
    res := res.append res'
  res := res.insertionSort (λ d d' => d.num < d'.num)
  IO.println s!"done."
  let filename := "out.txt"
  IO.println s!"writing to {filename}"
  IO.FS.withFile filename IO.FS.Mode.write λ handle => do
    for data in res do
      handle.putStrLn data.name
      handle.putStrLn <| ", ".intercalate (data.polys.map toString).toList
      handle.putStrLn <| ", ".intercalate (data.polys'.map toString).toList
| _ =>
  throw <| IO.userError "Expecting exactly one argument"
