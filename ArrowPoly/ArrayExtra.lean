theorem not_or (p q) : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
⟨fun H => ⟨mt Or.inl H, mt Or.inr H⟩, fun ⟨hp, hq⟩ pq => pq.elim hp hq⟩

def Array.dropZeros (a : Array Int) : Array Int :=
  if h : a.isEmpty ∨ a.back ≠ 0 then
    a
  else
    have : size a - 1 < size a := by
      simp [not_or, isEmpty] at h
      show _ ≤ _
      simp [h.1, Nat.sub_succ, Nat.succ_pred]
    dropZeros a.pop
termination_by _ => a.size

/-
def Array.dropZeros (a : Array Int) : Array Int :=
  let rec aux : Nat → Array Int → Array Int
          | 0, _ => a
          | n+1, a => if a.back ≠ 0 then a else aux n a.pop
  aux a.size a
-/

@[simp]
theorem not_not (p : Prop) : ¬¬p ↔ p := by
  cases Classical.em p with
  | inl h => simp [h]
  | inr h => simp [h]

theorem Array.back?_eq_of_size_eq_zero (a : Array Int) (h : a.size = 0) : a.back? = none := by
  simp [back?, h]
  cases a
  rename_i xs
  cases xs with
  | nil => rfl
  | cons x xs => cases h

theorem Array.back?_dropZeros (a : Array Int) : a.dropZeros.back? ≠ some 0 := by
  rw [dropZeros]
  simp []
  split
  rename_i h
  simp [isEmpty] at h
  cases h with
  | inl h => simp [Array.back?_eq_of_size_eq_zero _ h]
  | inr h =>
    simp [back?, get?]
    split
    rename_i h'
    simp
    simp [back, get!, getD, h'] at h
    exact h
    simp
  rename_i h
  have : size a - 1 < size a := by
    simp [not_or, isEmpty] at h
    have : ∃ n, size a = n := ⟨_, rfl⟩
    cases this with
    | intro n h' =>
      simp [h']
      simp [h'] at h
      cases n
      exact False.elim (h.1 rfl)
      show _ ≤ _
      apply Nat.le_refl
  apply back?_dropZeros
termination_by _ => a.size

theorem List.concat_cons (x : α) (xs : List α) (y : α) :
  (x :: xs).concat y = x :: xs.concat y := rfl

@[simp]
theorem List.get_concat (x y : α) (xs : List α) (i : Fin (xs.concat y).length) :
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
    have := List.get_concat x y xs ⟨xs.length, this⟩
    rw [ih] at this
    exact this

@[simp]
theorem Array.back?_push (a : Array α) [Inhabited α] (x : α) : (a.push x).back? = some x := by
  simp [back?, push, get?, get]
  split
  rename_i h
  simp [Nat.add_sub_self_right]
  
  rename_i h
  apply h
  simp [Nat.add_sub_self_right]
  apply Nat.lt_succ_self

@[inline] def Array.get!? (a : Array α) (i : Nat) (default : α) : α :=
if h : i < a.size then a.get ⟨i, h⟩ else default

@[specialize] def Array.zipWith'Aux [Inhabited α] [Inhabited β]
  (f : α → β → γ) (as : Array α) (bs : Array β) (i : Nat) (cs : Array γ) : Array γ :=
  if h : i < max as.size bs.size then
    zipWith'Aux f as bs (i+1) <| cs.push <| f (as.get!? i default) (bs.get!? i default)
  else
    cs
termination_by _ => max as.size bs.size - i

@[inline] def Array.zipWith' [Inhabited α] [Inhabited β]
  (as : Array α) (bs : Array β) (f : α → β → γ) : Array γ :=
  zipWith'Aux f as bs 0 #[]

@[specialize] def Array.lexicographicAux [Ord α] [Inhabited α] (as bs : Array α) (i : Nat) : Ordering :=
  if h : i < max as.size bs.size then
    match compare (as.get!? i default) (bs.get!? i default) with
    | .eq => lexicographicAux as bs (i+1)
    | c => c
  else
    .eq
termination_by _ => max as.size bs.size - i

@[inline] def Array.lexicographic [Ord α] [Inhabited α] : Ord (Array α) where
  compare as bs := Array.lexicographicAux as bs 0

inductive Merge α
| left (x : α)
| right (x : α)
| both (x y : α)

section merge
variable (f : α → β) [Ord β] (g : Array γ → Merge α → Array γ) 

def Array.mergeByAuxLeft (as : Array α) (i : Nat) (cs : Array γ) : Array γ :=
  if h : i < as.size then
      mergeByAuxLeft as (i+1) <| g cs (.left <| as.get ⟨i, h⟩)
  else cs
termination_by _ => as.size - i

def Array.mergeByAuxRight (bs : Array α) (j : Nat) (cs : Array γ) : Array γ :=
  if h : j < bs.size then
      mergeByAuxRight bs (j+1) <| g cs (.right <| bs.get ⟨j, h⟩)
  else cs
termination_by _ => bs.size - j

@[specialize]
def Array.mergeByAux (as bs : Array α) (i j : Nat) (cs : Array γ) : Array γ :=
  if h : i < as.size ∧ j < bs.size then
    match compare (f <| as.get ⟨i, h.1⟩) (f <| bs.get ⟨j, h.2⟩) with
    | .lt =>
      have : size as - (i + 1) + (size bs - j) < size as - i + (size bs - j) := by
        apply Nat.add_lt_add_right
        show _ ≤ _
        simp [Nat.sub_succ, Nat.succ_pred, Nat.sub_ne_zero_of_lt h.1]
      mergeByAux as bs (i+1) j <| g cs <| .left (as.get ⟨i, h.1⟩)
    | .eq =>
      have : size as - (i + 1) + (size bs - (j + 1)) < size as - i + (size bs - j) := by
        apply Nat.add_lt_add
        repeat
          show _ ≤ _
          simp [Nat.sub_succ, Nat.succ_pred, Nat.sub_ne_zero_of_lt, h.1, h.2]
      mergeByAux as bs (i+1) (j+1) <| g cs <| .both (as.get ⟨i, h.1⟩) (bs.get ⟨j, h.2⟩)
    | .gt =>
      have : size as - i + (size bs - (j + 1)) < size as - i + (size bs - j) := by
        apply Nat.add_lt_add_left
        show _ ≤ _
        simp [Nat.sub_succ, Nat.succ_pred, Nat.sub_ne_zero_of_lt h.2]
      mergeByAux as bs i (j+1) <| g cs <| .right (bs.get ⟨j, h.2⟩)
  else if i < as.size then
    mergeByAuxLeft g as i cs
  else if j < bs.size then
    mergeByAuxRight g bs j cs
  else cs
termination_by _ => (as.size - i) + (bs.size - j)

@[inline]
def Array.mergeBy (f : α → β) [Ord β]
  (g : Array γ → Merge α → Array γ) (as bs : Array α) : Array γ :=
  .mergeByAux f g as bs 0 0 #[]

end merge