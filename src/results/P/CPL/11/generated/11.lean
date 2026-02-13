

theorem exists_compact_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ K, IsCompact K ∧ K ⊆ A := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_⟩
  intro x hx
  cases hx