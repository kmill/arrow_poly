theorem not_or (p q) : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
⟨fun H => ⟨mt Or.inl H, mt Or.inr H⟩, fun ⟨hp, hq⟩ pq => pq.elim hp hq⟩

@[simp]
theorem not_not (p : Prop) : ¬¬p ↔ p := by
  cases Classical.em p with
  | inl h => simp [h]
  | inr h => simp [h]

theorem Function.mt {p q : Prop} (f : p → q) : ¬ q → ¬ p :=
λ hnq p => (hnq (f p)).elim