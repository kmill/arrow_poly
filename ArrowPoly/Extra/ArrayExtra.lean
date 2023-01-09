import ArrowPoly.Extra.NatExtra
import ArrowPoly.Extra.ListExtra
import ArrowPoly.Extra.LogicExtra

theorem List.toArrayAux_eq (xs ys : List α) :
  xs.toArrayAux (Array.mk ys) = Array.mk (ys ++ xs) :=
by
  induction xs generalizing ys with
  | nil => simp [toArrayAux]
  | cons x xs ih =>
    simp [toArrayAux]
    rw [ih]
    simp [Array.push, List.concat_append]

@[simp]
theorem List.toArray_eq (xs : List α) : xs.toArray = Array.mk xs :=
by
  induction xs using List.concat_ind with
  | nil => rfl
  | concat xs x ih =>
    simp [toArray, toArrayAux, Array.mkEmpty, List.toArrayAux_eq]

theorem Array.foldlM.loop_step {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (f : β → α → m β) (xs : List α) (i j : Nat) (h : xs.length ≤ i + j) (b : β) :
  Array.foldlM.loop f (Array.mk xs) xs.length (by simp) i j b
  = (xs.drop j).foldlM f b :=
by
  unfold foldlM.loop
  split
  · split
    · simp at h
      cases Nat.not_le_of_gt ‹_› h
    next h' j' i =>
      rw [Nat.succ_add] at h
      simp [foldlM.loop_step f xs i (j + 1) h]
      simp [← List.get_drop_eq_drop _ _ h']
      rfl
  · rw [List.drop_of_length_le]; rfl
    exact Nat.ge_of_not_lt ‹_›

theorem Array.foldlM_eq {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
  (f : β → α → m β) (init : β) (xs : List α) :
  (Array.mk xs).foldlM f init = xs.foldlM f init :=
by simp [foldlM, Array.foldlM.loop_step, List.drop]

theorem Array.map_eq (xs : List α) (f : α → β) :
  (Array.mk xs).map f = Array.mk (xs.map f) :=
by
  simp [map, mapM, Array.foldlM_eq, mkEmpty, push]
  induction xs using List.concat_ind with
  | nil => rfl
  | concat xs x ih =>
    rw [List.foldlM_concat_Id]
    simp [List.map_concat, Id.run]
    simp [Id.run] at ih
    rw [ih]

theorem Array.back_eq_of_back?_eq [Inhabited α] {a : Array α} (h : a.back? = some x) :
  a.back = x :=
by
  simp [back?, get?, get] at h
  split at h
  next h' =>
    cases h
    simp [back, get!, getD, h', get]
    rfl
  next =>
    cases h


/-- Pop off trailing zeros -/
def Array.popZeros (a : Array Int) : Array Int :=
  if h : a.isEmpty ∨ a.back ≠ 0 then
    a
  else
    have : size a - 1 < size a := by
      simp [not_or, isEmpty, ← Nat.pred_le_self_iff_ne_zero] at h
      exact h.1
    popZeros a.pop
termination_by _ => a.size

theorem Array.back?_eq_of_size_eq_zero (a : Array Int) (h : a.size = 0) : a.back? = none := by
  simp [back?, h]
  cases a
  rename_i xs
  cases xs with
  | nil => rfl
  | cons x xs => cases h

theorem Array.back?_popZeros (a : Array Int) : a.popZeros.back? ≠ some 0 := by
  rw [popZeros]
  simp []
  split
  next h =>
    simp [isEmpty] at h
    cases h with
    | inl h => simp [Array.back?_eq_of_size_eq_zero _ h]
    | inr h => exact Array.back_eq_of_back?_eq.mt h
  next h =>
    have : size a - 1 < size a := by
      simp [not_or, isEmpty] at h
      apply Nat.pred_le_self_of_ne_zero _ h.1
    apply back?_popZeros
termination_by _ => a.size

@[simp]
theorem Array.size_mk (xs : List α) : (Array.mk xs).size = xs.length := rfl

@[simp]
theorem Array.back?_push (a : Array α) [Inhabited α] (x : α) : (a.push x).back? = some x := by
  simp [back?, push, get?, getElem, get]
  split
  next h =>
    simp [Nat.add_sub_cancel]
  next h =>
    apply h
    simp [Nat.add_sub_self_right]
    apply Nat.lt_succ_self

/-- Get the element if the index is in range, else return `default`. -/
@[inline] def Array.get!? (a : Array α) (i : Nat) (default : α) : α :=
if h : i < a.size then a.get ⟨i, h⟩ else default

@[specialize] def Array.zipWith'Aux [Inhabited α] [Inhabited β]
  (f : α → β → γ) (as : Array α) (bs : Array β) (i : Nat) (cs : Array γ) : Array γ :=
  if h : i < max as.size bs.size then
    zipWith'Aux f as bs (i+1) <| cs.push <| f (as.get!? i default) (bs.get!? i default)
  else
    cs
termination_by _ => max as.size bs.size - i

/-- Like `Array.zipWith`, but extend the arrays with `default` so they match lengths. -/
@[inline] def Array.zipWith' [Inhabited α] [Inhabited β]
  (as : Array α) (bs : Array β) (f : α → β → γ) : Array γ :=
  zipWith'Aux f as bs 0 (Array.mkEmpty <| max as.size bs.size)

@[specialize] def Array.lexicographicAux [Ord α] [Inhabited α] (as bs : Array α) (i : Nat) : Ordering :=
  if i < max as.size bs.size then
    match compare (as.get!? i default) (bs.get!? i default) with
    | .eq => lexicographicAux as bs (i+1)
    | c => c
  else
    .eq
termination_by _ => max as.size bs.size - i

@[inline] def Array.lexicographic [Ord α] [Inhabited α] : Ord (Array α) where
  compare as bs := Array.lexicographicAux as bs 0

inductive Merge (α : Type _)
| left (x : α)
| right (x : α)
| both (x y : α)
deriving Repr, DecidableEq

section merge
variable (f : α → β) [Ord β] (g : γ → Merge α → γ) 

def Array.mergeByAuxLeft (as : Array α) (i : Nat) (cs : γ) : γ :=
  if h : i < as.size then
      mergeByAuxLeft as (i+1) <| g cs (.left <| as.get ⟨i, h⟩)
  else cs
termination_by _ => as.size - i

def Array.mergeByAuxRight (bs : Array α) (j : Nat) (cs : γ) : γ :=
  if h : j < bs.size then
      mergeByAuxRight bs (j+1) <| g cs (.right <| bs.get ⟨j, h⟩)
  else cs
termination_by _ => bs.size - j

@[specialize]
def Array.mergeByAux (as bs : Array α) (i j : Nat) (cs : γ) : γ :=
  if h : i < as.size ∧ j < bs.size then
    match compare (f <| as.get ⟨i, h.1⟩) (f <| bs.get ⟨j, h.2⟩) with
    | .lt =>
      have : size as - (i + 1) + (size bs - j) < size as - i + (size bs - j) := by
        apply Nat.add_lt_add_right
        show Nat.succ _ ≤ _
        simp [Nat.sub_succ, Nat.succ_pred, Nat.sub_ne_zero_of_lt h.1]
      mergeByAux as bs (i+1) j <| g cs <| .left (as.get ⟨i, h.1⟩)
    | .eq =>
      have : size as - (i + 1) + (size bs - (j + 1)) < size as - i + (size bs - j) := by
        apply Nat.add_lt_add
        repeat
          show Nat.succ _ ≤ _
          simp [Nat.sub_succ, Nat.succ_pred, Nat.sub_ne_zero_of_lt, h.1, h.2]
      mergeByAux as bs (i+1) (j+1) <| g cs <| .both (as.get ⟨i, h.1⟩) (bs.get ⟨j, h.2⟩)
    | .gt =>
      have : size as - i + (size bs - (j + 1)) < size as - i + (size bs - j) := by
        apply Nat.add_lt_add_left
        show Nat.succ _ ≤ _
        simp [Nat.sub_succ, Nat.succ_pred, Nat.sub_ne_zero_of_lt h.2]
      mergeByAux as bs i (j+1) <| g cs <| .right (bs.get ⟨j, h.2⟩)
  else if i < as.size then
    mergeByAuxLeft g as i cs
  else if j < bs.size then
    mergeByAuxRight g bs j cs
  else cs
termination_by _ => (as.size - i) + (bs.size - j)

/-- Assuming the arrays are sorted with respect to `f`, merge them fold the result
using `g`.  -/
@[inline]
def Array.mergeBy (init : γ) (as bs : Array α) : γ :=
  Array.mergeByAux f g as bs 0 0 init

--#eval Array.mergeBy id Array.push #[] #[1,2,4] #[1,3]

end merge

@[simp] theorem Array.empty_size : (#[] : Array α).size = 0 := rfl

theorem Array.get_push (as : Array α) (a : α) (i : Nat) (h : i < as.size) :
  (as.push a).get ⟨i, by { simp; apply Nat.lt.step h }⟩ = as.get ⟨i, h⟩ :=
by
  simp [get, push]
  cases as with
  | mk lst => apply List.get_concat

@[simp]
theorem Array.get_push_last (as : Array α) (a : α) :
  (as.push a).get ⟨as.size, by { simp; apply Nat.lt_succ_self }⟩ = a :=
by simp [get, push]

@[simp] theorem Array.size_map (as : Array α) (f : α → β) :
  (as.map f).size = as.size :=
by
  cases as with | mk xs =>
  simp [Array.map_eq]


theorem Array.getOp_map [Inhabited α] [Inhabited β] (as : Array α) (f : α → β) (i : Nat)
  (h : f default = default) :
  (as.map f)[i]! = f as[i]! :=
by
  cases as with | mk lst =>
  generalize ha : map f (Array.mk lst) = x
  rw [map_eq] at ha
  subst x
  simp [getElem!, getElem, get!, getD, size, get]
  split
  · simp [List.get_map]
  · exact h.symm

theorem Array.get_map (as : Array α) (f : α → β) (i : Nat) {h h'} :
  (as.map f).get ⟨i, h⟩ = f (as.get ⟨i, h'⟩) :=
by
  generalize h : map f as = x, h' : Fin.mk i h = y
  cases as with | mk lst =>
  rw [map_eq] at h
  subst h
  simp [get]
  rw [List.get_map]
  apply congrArg
  apply congrArg
  simp
  cases y
  simp
  rename_i a b c
  generalize hm : size (map f (Array.mk lst)) = m
  generalize hn : size (Array.mk (lst.map f)) = n
  have : HEq (⟨i, by { subst hm; exact h }⟩ : Fin m) (⟨b, by { subst hn; exact c }⟩ : Fin n) := by
    subst hm hn
    exact h'
  simp [size] at hm
  simp at hn
  subst hm hn
  cases this
  rfl

section strict_increasing
variable [LT α]

def Array.allTrue (as : Array α) (f : α → Prop) : Prop :=
∀ (i : Fin as.size), f (as.get i)

def Array.strictIncreasing (as : Array α) : Prop :=
∀ (i j : Fin as.size), i < j → as.get i < as.get j

theorem Array.strictIncreasing_empty : (#[] : Array α).strictIncreasing :=
by
  intros i j hij
  cases i
  rename_i h
  exact (Nat.not_lt_zero _ h).elim

theorem Array.strictIncreasing_singleton (x : α) : #[x].strictIncreasing :=
by
  intros i j hij
  cases i with | mk i hi =>
  cases j with | mk j hj =>
  have hi : i < 1 := hi
  have hj : j < 1 := hj
  simp at hi hj
  subst i j
  have : 0 < 0 := hij
  simp at this

theorem Array.strictIncreasing_push (as : Array α) (a : α) :
  (as.push a).strictIncreasing ↔ as.strictIncreasing ∧ as.allTrue (· < a) where
  mp := by
    intro h
    apply And.intro
    · intros i j hij
      specialize h ⟨i, _⟩ ⟨j, _⟩ hij
      · simp [Nat.lt.step i.isLt]
      · simp [Nat.lt.step j.isLt]
      · simp [Array.get_push as a j j.isLt] at h
        rw [Array.get_push as a i _] at h
        exact h
    · intro i
      specialize h ⟨i, _⟩ ⟨as.size, _⟩ i.isLt
      · simp [Nat.lt.step i.isLt]
      · simp [Nat.lt_succ_self]
      · simp [Array.get_push as a i i.isLt, Array.get_push_last] at h
        exact h
  mpr := by
    intros h i j hij
    cases h with | intro h h' =>
      cases Classical.em (i < as.size) with
      | inl h'' =>
        rw [Array.get_push as a i h'']
        cases Classical.em (j < as.size) with
        | inl h''' =>
          rw [Array.get_push as a j h''']
          exact h _ _ hij
        | inr h''' =>
          cases j with | mk j hj =>
          simp at hj
          cases Nat.eq_of_not_lt_and_lt_succ h''' hj
          simp
          apply h'
      | inr h'' =>
        cases i with | mk i hi =>
        simp at hi
        cases Nat.eq_of_not_lt_and_lt_succ h'' hi
        simp at *
        cases j with | mk j hj =>
        simp at hij
        cases Classical.em (j < as.size) with
        | inl h''' =>
          have hij' := Nat.lt_trans hij h'''
          simp at hij'
        | inr h''' =>
          simp at hj
          cases Nat.eq_of_not_lt_and_lt_succ h''' hj
          have : List.length as.data < List.length as.data := hij
          simp at this



--theorem Array.strictIncreasing_pop (a : Array α) (h : a.strictIncreasing) :
--  a.pop.strictIncreasing := by

--theorem Array.get_pop (as : Array α) (i : Nat) (h : i < as.)

theorem Array.push_pop (as : Array α) (h : as.size - 1 < as.size) :
  as.pop.push (as.get ⟨as.size - 1, h⟩) = as :=
by
  cases as with | mk xs =>
  simp [push, pop, get, size]
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons x' xs =>
      simp [List.dropLast, List.concat, List.get]
      simp [Nat.pred_succ] at ih
      have : ∀ (k : Nat), k.succ - 1 = k := λ k => rfl
      simp [size, this] at h
      apply ih h

section ind

theorem Array.eq_empty_of_isEmpty {as : Array α} (h : as.isEmpty) : as = #[] :=
by
  cases as with | mk lst =>
  cases lst with
  | nil => rfl
  | cons x xs => simp [isEmpty] at h

theorem Array.ind_push {motive : Array α → Prop}
  (empty : motive #[])
  (push : (as : Array α) → (a : α) → motive as → motive (as.push a))
  (as : Array α) : motive as :=
if h : as.isEmpty then
  by
    have h := Array.eq_empty_of_isEmpty h
    cases h
    exact empty
else
  by
    simp [isEmpty] at h
    have : size as - 1 < size as := Nat.pred_lt h
    have h' := push as.pop (as.get ⟨as.size - 1, this⟩)
    specialize h' (ind_push (motive := motive) empty push as.pop)
    simp at h'
    rw [Array.push_pop as this] at h'
    exact h'
termination_by _ => as.size

end ind

def Array.enumerate (as : Array α) : Array (Nat × α) :=
(as.foldl (λ (acc : Nat × Array (Nat × α)) a =>
  (acc.1 + 1, acc.2.push (acc.1, a))) (0, Array.mkEmpty as.size)).2

@[specialize] private partial def Array.binInsertAux'
    {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α]
    (lt : α → α → Bool)
    (merge : α → m (Option α))
    (add : Unit → m α)
    (as : Array α)
    (k : α) : Nat → Nat → m (Array α)
  | lo, hi =>
    -- as[lo] < k < as[hi]
    let mid    := (lo + hi)/2
    let midVal := as.get! mid
    if lt midVal k then
      if mid == lo then do let v ← add (); pure <| as.insertAt! (lo+1) v
      else binInsertAux' lt merge add as k mid hi
    else if lt k midVal then
      binInsertAux' lt merge add as k lo mid
    else do
      match ← merge (as.get! mid) with
      | none => return as.eraseIdx mid
      | some v => return as.set! mid v

-- version to have merge that is able to delete
@[specialize] def Array.binInsertM' {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α]
    (lt : α → α → Bool)
    (merge : α → m (Option α))
    (add : Unit → m α)
    (as : Array α)
    (k : α) : m (Array α) :=
  if as.isEmpty then do let v ← add (); pure <| as.push v
  else if lt k (as.get! 0) then do let v ← add (); pure <| as.insertAt 0 v
  else if !lt (as.get! 0) k then do
    match ← merge (as.get! 0) with
    | none => return as.eraseIdx 0
    | some k' => return as.set! 0 k'
  else if lt as.back k then do let v ← add (); pure <| as.push v
  else if !lt k as.back then do
    match ← merge as.back with
    | none => return as.pop
    | some k' => return as.set! (as.size - 1) k'
  else Array.binInsertAux' lt merge add as k 0 (as.size - 1)
