

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  simpa using P3_of_open (A := interior A) isOpen_interior

theorem exists_P2_subset_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : ∃ B, B ⊆ A ∧ P2 B := by
  refine ⟨interior A, interior_subset, ?_⟩
  exact P2_interior (X := X) (A := A)