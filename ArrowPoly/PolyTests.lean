import ArrowPoly.Poly
import ArrowPoly.LSpec

#lspec do
  test "zero" <| toString (0 : Poly) = "Poly[]"
  test "one" <| toString (1 : Poly) = "Poly[1*M[]]"
  test "A" <| toString (Poly.A) = "Poly[1*M[1]]"
  test "A*A" <| toString (Poly.A * Poly.A) = "Poly[1*M[2]]"
  test "A+A" <| toString (Poly.A + Poly.A) = "Poly[2*M[1]]"
  test "3*A" <| toString (3 * Poly.A) = "Poly[3*M[1]]"
  test "3+A" <| toString (3 + Poly.A) = "Poly[3*M[], 1*M[1]]"
  test "1+1" <| toString ((1 : Poly) + 1) = "Poly[2*M[]]"
  test "1+A-1" <| toString (1 + Poly.A - 1) = "Poly[1*M[1]]"
  test "A+1-1" <| toString (Poly.A + 1 - 1) = "Poly[1*M[1]]"
  test "(1-A)^3" <| toString ((1 - Poly.A)^3) = "Poly[1*M[], -3*M[1], 3*M[2], -1*M[3]]"
  test "(A+K_1)^3" <| toString ((Poly.A + Poly.K 1)^3) = "Poly[1*M[0,3], 3*M[1,2], 3*M[2,1], 1*M[3]]"
  test "toList (1+A)^6" <| ((1 + Poly.A)^6 : Poly).toList =
    [(1, []), (6, [1]), (15, [2]), (20, [3]), (15, [4]), (6, [5]), (1, [6])]
  test "toList (A-K_1)^6" <| ((Poly.A - Poly.K 1) ^ 6 : Poly).toList =
    [(1, [0, 6]), (-6, [1, 5]), (15, [2, 4]), (-20, [3, 3]), (15, [4, 2]), (-6, [5, 1]), (1, [6])]
  test "fromList toList" <| Poly.fromList (Poly.A + Poly.A + Poly.K 1).toList = 2 * Poly.A + Poly.K 1
  test "A ≠ 1" <| Poly.A ≠ 1
  test "A ≠ 0" <| Poly.A ≠ 0
  test "A ≠ K_1" <| Poly.A ≠ Poly.K 1
  test "K_0 = 1" <| Poly.K 0 = 1
  test "A^3 test" <| Poly.A 3 - Poly.A^3 = 0
  test "mul zero" <| (1 - Poly.A)^3 * 0 = 0
  test "mul one" <| (1 - Poly.A)^3 * 1 = (1 - Poly.A)^3
  test "zero mul" <| (0 : Poly) * (1 - Poly.A)^3 = 0
  test "one mul" <| (1 : Poly) * (1 - Poly.A)^3 = (1 - Poly.A)^3
  test "subst_K_one 1" <| (Poly.A ^ 3 * Poly.K 2).subst_K_one = Poly.A ^ 3
  test "subst_K_one 2" <| (Poly.K 2 + Poly.K 3).subst_K_one = 2
  test "subst_K_one 3" <| (0 : Poly).subst_K_one = 0
  test "pow cancel 1" <| Poly.A * Poly.A (-1) = 1
  test "pow cancel 2" <| Poly.A (-1) * Poly.A = 1
  test "pow cancel 3" <| Poly.A (-1) * (Poly.K 1 + Poly.K 2) * (Poly.K 1 + Poly.K 2) * Poly.A
    = Poly.K 2 ^ 2 + 2 * Poly.K 1 * Poly.K 2 + Poly.K 1 ^ 2

#lspec do
  let a : Poly := Monomial.mk #[1, 2] 2
  let b : Poly := Monomial.mk #[3] 3
  test "eq zero 1" <| (a * b + b) - ((a + 1) * b) = 0
  test "eq zero 2" <| (a * b + a) - (a * (b + 1)) = 0

#lspec do
  test "mirror 1" <| (0 : Poly).mirror = 0
  test "mirror 2" <| ∀ (n : Nat), n < 5 → (n : Poly).mirror = n
  test "mirror 3" <| ∀ (n : Nat), n < 5 → (n + Poly.A : Poly).mirror = (n + Poly.A (-1) : Poly)
  test "mirror 4" <| (1 + Poly.A 3 + Poly.A (-5) + Poly.A 2 * Poly.K 1).mirror =
    1 + Poly.A (-3) + Poly.A 5 + Poly.A (-2) * Poly.K 1
