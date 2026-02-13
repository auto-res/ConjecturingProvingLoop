

theorem exists_P2_compact_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, K ⊆ A ∧ IsCompact K ∧ P2 K := by
  refine ⟨(∅ : Set X), Set.empty_subset _, isCompact_empty, P2_empty⟩

theorem exists_P3_compact_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, K ⊆ A ∧ IsCompact K ∧ P3 K := by
  refine ⟨(∅ : Set X), Set.empty_subset _, isCompact_empty, P3_empty⟩