theorem Nat.eq_zero_or_eq_zero_of_mul_eq_zero (a b : Nat) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  cases a <;> cases b <;> simp <;> try cases h

@[simp]
theorem Int.ofNat_eq_zero (n : Nat) : Int.ofNat n = 0 ↔ n = 0 := by
  apply Iff.intro
  repeat intro h; cases h; rfl

theorem Int.eq_zero_or_eq_zero_of_mul_eq_zero : (a b : Int) → a * b = 0 → a = 0 ∨ b = 0
| Int.ofNat m, Int.ofNat n, h => by
  have h : ofNat (m * n) = 0 := h
  simp at h
  cases Nat.eq_zero_or_eq_zero_of_mul_eq_zero _ _ h
  simp [*]
  simp [*]
| Int.ofNat 0, Int.negSucc n, h => by simp
| Int.ofNat (m+1), Int.negSucc n, h => by cases h
| Int.negSucc n, Int.ofNat 0, h => by simp
| Int.negSucc n, Int.ofNat (m+1), h => by cases h
| Int.negSucc m, Int.negSucc n, h => by cases h

@[simp]
theorem Int.neg_eq_zero : (x : Int) → -x = 0 ↔ x = 0
| Int.ofNat 0 => Iff.rfl
| Int.ofNat (n+1) => by
  show Int.negSucc _ = 0 ↔ _
  simp
  intro x
  cases x
| Int.negSucc n => by
  show Int.ofNat _ = 0 ↔ _
  simp

@[simp]
theorem Int.neg_inj : (a b : Int) → -a = -b ↔ a = b
| Int.ofNat 0, Int.ofNat 0 => by simp
| Int.ofNat (m+1), Int.ofNat 0 => by apply Iff.intro; repeat intro h; cases h
| Int.ofNat 0, Int.ofNat (n+1) => by apply Iff.intro; repeat intro h; cases h
| Int.ofNat (m+1), Int.ofNat (n+1) => by show Int.negSucc _ = Int.negSucc _ ↔ _; simp
| Int.ofNat 0, Int.negSucc n => by simp; intro h; cases h
| Int.ofNat (m+1), Int.negSucc n => by simp; intro h; cases h
| Int.negSucc n, Int.ofNat 0 => by simp; intro h; cases h
| Int.negSucc n, Int.ofNat (m+1) => by simp; intro h; cases h
| Int.negSucc m, Int.negSucc n => by
  show Int.ofNat m.succ = n.succ ↔ _
  simp
