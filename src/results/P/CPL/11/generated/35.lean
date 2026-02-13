

theorem P1_compact_subset {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ K, IsCompact K ∧ K ⊆ A := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_⟩
  exact Set.empty_subset _