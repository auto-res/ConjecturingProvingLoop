

theorem exists_P3_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → ∃ B, B ⊆ A ∧ P3 B := by
  intro _hP1
  refine ⟨interior A, interior_subset, ?_⟩
  simpa using (P3_interior (A := A))

theorem exists_P1_superset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → ∃ B, A ⊆ B ∧ P1 B := by
  intro hP3
  refine ⟨interior (closure (A : Set X)), ?_, ?_⟩
  · -- `A ⊆ interior (closure A)`
    exact hP3
  · -- `P1 (interior (closure A))`
    simpa using (P1_interior (A := closure (A : Set X)))