import ArrowPoly.Extra.NatExtra

theorem List.concat_append : ys.concat x ++ xs = ys ++ x :: xs :=
  match ys with
    | nil => rfl
    | cons y ys => by simp [concat, concat_append]

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
  match xs, i with
    | nil, _ => by cases h
    | cons .., 0 => by simp [List.get]
    | cons x xs, i + 1 => by
      simp [List.get]
      simp at h
      exact get_concat _ _ _ h

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
| [], _ => 0
| x :: xs, a => (if x == a then 1 else 0) + xs.count a

inductive List.nodup : List α → Prop
| nil : nodup []
| cons (x : α) (xs : List α) (h : ¬ x ∈ xs) : nodup (x :: xs)

@[simp]
theorem List.length_drop (n : Nat) (xs : List α) : (xs.drop n).length = xs.length - n :=
by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => simp [List.drop]
    | cons x xs => simp [List.drop, Nat.succ_sub_succ, ih]

theorem List.drop_of_length_le {n : Nat} {xs : List α} (h : xs.length ≤ n) : xs.drop n = [] :=
by
  rw [← Nat.sub_eq_zero_iff] at h
  have := xs.length_drop n
  rw [h, List.length_eq_zero_iff] at this
  assumption

theorem List.get_drop (xs : List α) (m n : Nat) (h h') :
  (xs.drop m).get ⟨n, h⟩ = xs.get ⟨m + n, h'⟩ :=
by
  induction xs generalizing m n with
  | nil =>
    simp at h
    exact (Nat.not_lt_zero _ h).elim
  | cons x xs ih =>
    cases m with
    | zero => simp [drop]
    | succ m =>
      simp [drop, Nat.succ_add, get]
      rw [ih]

theorem List.drop_drop (xs : List α) (m n : Nat) :
  (xs.drop m).drop n = xs.drop (n + m) :=
by
  induction xs generalizing m n with
  | nil =>
    simp
  | cons x xs ih =>
    cases m with
    | zero => simp [drop]
    | succ m => simp [drop, ih]

theorem List.map_concat (xs : List α) (x : α) (f : α → β) :
  (xs.concat x).map f = (xs.map f).concat (f x) :=
by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [concat, map, ih]

theorem List.foldlM_concat_Id {α : Type u} {β : Type v}
  (f : β → α → Id β) (init : β) (xs : List α) (x : α) :
  (xs.concat x).foldlM f init = (do let b ← xs.foldlM f init; f b x) :=
by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => simp [concat, List.foldlM, ih]

theorem List.get_map (xs : List α) (f : α → β) (i : Nat) (h) :
  (xs.map f).get ⟨i, h⟩ = f (xs.get ⟨i, by { simp at h; exact h }⟩) :=
by
  induction xs generalizing i with
  | nil =>
    simp at h
    exact (Nat.not_lt_zero _ h).elim
  | cons x xs ih =>
    cases i
    · rfl
    · simp [map, get, ih]
