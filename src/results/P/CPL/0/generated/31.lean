

theorem exists_P2_open_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, IsOpen U ∧ A ⊆ U ∧ P2 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, Set.subset_univ A, ?_⟩
  simpa using (P2_univ : P2 (Set.univ : Set X))