

theorem exists_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P1 B := by
  exact ⟨(∅ : Set X), Set.empty_subset _, P1_empty⟩

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  unfold P3
  intro x hx
  cases hx