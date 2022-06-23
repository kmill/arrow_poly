import ArrowPoly.Extra.ListExtra
import ArrowPoly.Extra.ArrayExtra
import ArrowPoly.LSpec

#lspec do
  test "count 1" <| [1,2,3].count 3 = 1
  test "count 2" <| [1,2,3,2,3].count 3 = 2

#lspec do
  test "popZeros empty" <| #[].popZeros = #[]
  test "popZeros no zeros" <| #[1,2,3].popZeros = #[1,2,3]
  test "popZeros one zero" <| #[1,2,3,0].popZeros = #[1,2,3]
  test "popZeros zeros" <| #[1,2,3,0,0,0].popZeros = #[1,2,3]
  test "get!? in range" <| #[22].get!? 0 37 = 22
  test "get!? out of range" <| #[22].get!? 1 37 = 37
  test "zipWith' same length" <| #[1,2,3].zipWith' #[4,5,6] Prod.mk = #[(1,4), (2,5), (3, 6)]
  test "zipWith' first smaller" <| #[1].zipWith' #[4,5,6] Prod.mk = #[(1,4), (0,5), (0, 6)]
  test "zipWith' second smaller" <| #[1,2,3].zipWith' #[4] Prod.mk = #[(1,4), (2,0), (3, 0)]
  test "enumerate" <| #[10,11,12].enumerate = #[(0,10), (1,11), (2,12)]

section lexicographic
attribute [local instance] Array.lexicographic

#lspec do
  test "lex 1" <| compare #[1,2] #[1,2] == Ordering.eq
  test "lex 2" <| compare #[] #[1,2] == Ordering.lt
  test "lex 3" <| compare #[1,2] #[] == Ordering.gt
  test "lex 4" <| compare #[1] #[1,2] == Ordering.lt
  test "lex 5" <| compare #[1,2] #[1] == Ordering.gt
  test "lex 6" <| compare #[1,2] #[1,3] == Ordering.lt

end lexicographic

#lspec do
  let f (xs ys : Array Nat) := Array.mergeBy id Array.push #[] xs ys
  test "merge 1" <| f #[1,2] #[] = #[Merge.left 1, Merge.left 2]
  test "merge 2" <| f #[1] #[2] = #[Merge.left 1, Merge.right 2]
  test "merge 3" <| f #[2] #[1] = #[Merge.right 1, Merge.left 2]
  test "merge 4" <| f #[1,2,3] #[2,4] = #[Merge.left 1, Merge.both 2 2, Merge.left 3, Merge.right 4]

#lspec do
  let f (xs : Array Nat) (x : Nat) : Array Nat := Id.run <|
    Array.binInsertM' (· < ·) (λ y => if y = 2 then none else some y) (λ _ => x) xs x
  test "bin insert empty" <| f #[] 3 = #[3]
  test "bin insert exists delete" <| f #[2] 2 = #[]
  test "bin insert exists no delete" <| f #[1,5,10] 5 = #[1,5,10]
  test "bin insert not exists" <| f #[1,5,10] 6 = #[1,5,6,10]
  test "bin insert pre-start" <| f #[1,5,10] 0 = #[0,1,5,10]
  test "bin insert post-end" <| f #[1,5,10] 11 = #[1,5,10,11]
  test "bin insert start" <| f #[1,5,10] 1 = #[1,5,10]
  test "bin insert start delete" <| f #[2,5,10] 2 = #[5,10]
  test "bin insert end" <| f #[1,5,10] 10 = #[1,5,10]
  test "bin insert end delete" <| f #[0,1,2] 2 = #[0,1]
