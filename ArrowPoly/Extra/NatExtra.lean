import ArrowPoly.Extra.LogicExtra

@[simp] theorem Nat.lt_succ (m : Nat) : 0 < m.succ :=
by
  apply Nat.lt_succ_of_le
  simp

@[simp] theorem Nat.succ_lt_succ_iff (m n : Nat) : m.succ < n.succ ↔ m < n :=
⟨Nat.lt_of_succ_lt_succ, Nat.succ_lt_succ⟩

@[simp] theorem Nat.succ_le_succ_iff (m n : Nat) : m.succ ≤ n.succ ↔ m ≤ n :=
⟨Nat.le_of_succ_le_succ, Nat.succ_le_succ⟩

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

theorem Nat.ne_zero_of_sub_lt_self (m n : Nat) (h : m - n < m) : n ≠ 0 :=
by
  intro h
  cases h
  simp at h

theorem Nat.ne_zero_of_sub_succ_lt_self (m n : Nat) (h : m - n.succ < m) : m ≠ 0 :=
by
  intro h
  cases h
  simp at h

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

@[simp]
theorem Nat.add_eq_zero_iff {m n : Nat} : m + n = 0 ↔ m = 0 ∧ n = 0 := by
  cases m <;> cases n <;> simp <;> intro h <;> cases h

theorem Nat.sub_eq_zero_iff {m n : Nat} : m - n = 0 ↔ m ≤ n where
  mpr := Nat.sub_eq_zero_of_le
  mp := by
    induction m generalizing n with
    | zero => simp
    | succ m ih =>
      cases n with
      | zero => simp
      | succ n =>
        simp [Nat.succ_sub_succ]
        exact ih

theorem Nat.zero_lt_sub_iff (m n : Nat) : 0 < m - n ↔ n < m :=
by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    cases m with
    | zero => simp [Nat.not_lt]
    | succ m => simp [Nat.succ_sub_succ, ih]
