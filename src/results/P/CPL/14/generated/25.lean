

theorem exists_compact_P2_subset {X} [TopologicalSpace X] {A : Set X} : ∃ K, IsCompact K ∧ K ⊆ A ∧ P2 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, ?_⟩
  exact P2_empty (X := X)