import ArrowPoly.ArrowPoly
import ArrowPoly.LoadKnot

structure knot_data where
  name : String
  num : Nat
  polys : Array Poly
  polys' : Array Poly
  jpolys : Array Poly
  jpolys' : Array Poly

attribute [local instance] Array.lexicographic
local instance [Inhabited α] [Ord α] : LT (Array α) := ltOfOrd
local instance : LT Poly := ltOfOrd

def calculate_knot (cache : ATLCache) (num : Nat) (name : String) (pd : PD Nat) (bdry : Nat × Nat) :
  ATLCache × knot_data :=
Id.run do
  let mut cache := cache
  --let (pd, bdry) := pd.writhe_normalize bdry
  let mut polys : Array Poly := #[]
  for n in [1:4] do
    let (cache', p) := cache.cabled_arrow_poly n pd bdry
    polys := polys.push p
    cache := cache'
  let mut polys' := polys.map Poly.mirror
  if polys' < polys then
    (polys, polys') := (polys', polys)
  let mut jpolys := polys.map Poly.subst_K_one
  let mut jpolys' := polys'.map Poly.subst_K_one
  if jpolys' < jpolys then
    (jpolys, jpolys') := (jpolys', jpolys)
  return (cache, { name := name, num := num, polys := polys, polys' := polys', jpolys := jpolys, jpolys' := jpolys' })

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
    cache := cache'
    res := res.push knot
    IO.println s!"calculated for {knot.name}"
  return res

structure CalcOptions where
  input_file : Option String := none
  num_threads : Nat := 12
  max_crossings : Nat := 5
  only_knots : Option (Array String) := none

def CalcOptions.parse (opts : CalcOptions := {}) : List String → IO CalcOptions
| [] => return opts
| "-k" :: k :: args =>
  let knots := opts.only_knots.getD #[]
  parse {opts with only_knots := knots.push k} args
| fname :: args =>
  if opts.input_file.isNone then
    parse {opts with input_file := fname} args
  else
    throw <| IO.userError "Can only have one knot file."

def main (args : List String) : IO Unit := do
  let opts ← CalcOptions.parse {} args
  let fname ← match opts.input_file with
    | some fname => pure fname
    | none => throw <| IO.userError "Need to give knot file"
  IO.println s!"loading {fname}"
  let knots ← parseFile fname
  IO.println s!"loaded {knots.size} knots"
  let knots :=
    match opts.only_knots with
    | some only => knots.filter (λ k => only.contains k.1)
    | none => knots
  IO.println s!"processing {knots.size} knots"
  let nthreads := opts.num_threads
  let mut tasks := #[]
  for thread in [0 : nthreads] do
    tasks := tasks.push (← IO.asTask (knot_task knots opts.max_crossings nthreads thread))
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
      handle.putStrLn "arrow"
      handle.putStrLn <| ", ".intercalate (data.polys.map toString).toList
      handle.putStrLn <| ", ".intercalate (data.polys'.map toString).toList
      handle.putStrLn "jones"
      handle.putStrLn <| ", ".intercalate (data.jpolys.map toString).toList
      handle.putStrLn <| ", ".intercalate (data.jpolys'.map toString).toList
