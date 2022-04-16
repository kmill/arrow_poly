import ArrowPoly.Extra.LogicExtra

@[simp] theorem Nat.succ_lt_succ_iff (m n : Nat) : m.succ < n.succ ↔ m < n :=
⟨Nat.lt_of_succ_lt_succ, Nat.succ_lt_succ⟩

theorem Nat.pred_le_self_of_ne_zero (m : Nat) (h : m ≠ 0) : m - 1 < m :=
by cases m with
   | zero => exact (h rfl).elim
   | succ m => apply Nat.le_refl

theorem Nat.pred_le_self_iff_ne_zero (m : Nat) : m - 1 < m ↔ m ≠ 0 where
  mpr := Nat.pred_le_self_of_ne_zero m
  mp := by
    intro h
    cases m with
    | zero => cases h
    | succ m => simp

theorem Nat.eq_of_not_lt_and_lt_succ {m n : Nat} (hn : ¬ m < n) (h : m < n + 1) :
  m = n :=
Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.ge_of_not_lt hn)

@[simp] theorem Nat.lt_one_iff_eq_zero : {m : Nat} → m < 1 ↔ m = 0
| 0 => by simp
| m+1 => by
  simp [Nat.not_lt_zero]
  intro h
  cases h

protected theorem Nat.not_lt {n m : Nat} : ¬ n < m ↔ m ≤ n where
  mp := by
    intro h
    have := Nat.lt_or_ge n m
    simp [h] at this
    exact this
  mpr := by
    intros h h'
    have := Nat.lt_of_le_of_lt h h'
    simp at this

protected theorem Nat.not_le {n m : Nat} : ¬ n ≤ m ↔ m < n := by
  rw [← Nat.not_lt]
  simp [not_not]