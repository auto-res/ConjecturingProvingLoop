

theorem exists_open_P3_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, IsOpen U ∧ A ⊆ U ∧ P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, Set.subset_univ A, ?_⟩
  simpa using (P3_univ : P3 (Set.univ : Set X))

theorem exists_closed_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ C, IsClosed C ∧ C ⊆ A ∧ P1 C := by
  refine ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, P1_empty⟩