

theorem exists_P3_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ B : Set X, B ⊆ A ∧ P3 B := by
  refine ⟨(∅ : Set X), Set.empty_subset _, P3_empty⟩