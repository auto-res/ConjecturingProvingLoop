

theorem P1_exists_compact_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, IsCompact K ∧ K ⊆ A ∧ P1 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, P1_empty⟩

theorem P2_exists_compact_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, IsCompact K ∧ K ⊆ A ∧ P2 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, P2_empty⟩