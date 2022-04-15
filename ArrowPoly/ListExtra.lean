import ArrowPoly.NatExtra

theorem List.concat_cons (x : α) (xs : List α) (y : α) :
  (x :: xs).concat y = x :: xs.concat y := rfl

@[simp]
theorem List.get_concat_cons (x y : α) (xs : List α) (i : Fin (xs.concat y).length) :
  ((x :: xs).concat y).get i.succ = (xs.concat y).get i := rfl

@[simp]
theorem List.get_concat_last (xs : List α) (y : α) (h : xs.length < (xs.concat y).length) :
  (xs.concat y).get ⟨xs.length, h⟩ = y :=
by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have : length xs < length (concat xs y) := by
      simp
      apply Nat.lt_succ_self
    have := List.get_concat_cons x y xs ⟨xs.length, this⟩
    rw [ih] at this
    exact this

theorem List.get_concat (xs : List α) (a : α) (i : Nat) (h : i < xs.length) :
  (xs.concat a).get ⟨i, by { simp; apply Nat.lt.step h }⟩ = xs.get ⟨i, h⟩ :=
by
  induction xs generalizing i with
  | nil => cases h
  | cons x xs ih =>
    cases i with
    | zero => simp [List.get]
    | succ i =>
      simp [List.get]
      simp at h
      exact ih i h

theorem List.concat_dropLast_eq (xs : List α) (h : xs ≠ []) :
  xs.dropLast.concat (xs.getLast h) = xs :=
by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons x' xs =>
      simp [dropLast, concat_cons, getLast]
      apply ih

theorem List.length_eq_zero_iff : {xs : List α} → xs.length = 0 ↔ xs = nil
| [] => by simp
| x :: xs => by simp

theorem List.concat_ind {motive : List α → Prop}
  (nil : motive [])
  (concat : (xs : List α) → (x : α) → motive xs → motive (xs.concat x))
  (xs : List α) : motive xs :=
by
  generalize h : xs.length = n
  induction n generalizing xs with
  | zero =>
    simp [List.length_eq_zero_iff] at h
    cases h
    assumption
  | succ n ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simp at h
      cases h
      have := List.concat_dropLast_eq (x :: xs) (by simp)
      rw [← this]
      apply concat
      apply ih
      simp

def List.count [DecidableEq α] : List α → α → Nat
| [], a => 0
| x :: xs, a => (if x == a then 1 else 0) + xs.count a
