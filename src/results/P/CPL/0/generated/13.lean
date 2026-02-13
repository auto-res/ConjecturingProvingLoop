

theorem exists_open_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ U, IsOpen U ∧ U ⊆ A ∧ P1 U := by
  refine ⟨interior A, isOpen_interior, interior_subset, ?_⟩
  simpa using (P1_interior (A := A))

theorem exists_closed_P3_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ C, A ⊆ C ∧ IsClosed C ∧ P3 C := by
  refine ⟨Set.univ, ?_, isClosed_univ, ?_⟩
  · exact Set.subset_univ A
  · exact P3_univ