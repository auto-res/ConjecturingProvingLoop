

theorem exists_dense_P2_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ Dense B ∧ P2 B := by
  refine ⟨(Set.univ : Set X), Set.subset_univ A, dense_univ, ?_⟩
  simpa using (P2_univ : P2 (Set.univ : Set X))