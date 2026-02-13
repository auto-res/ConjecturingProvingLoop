

theorem exists_open_subset_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : ∃ U, IsOpen U ∧ A ⊆ U := by
  exact ⟨interior (closure (A : Set X)), isOpen_interior, hA⟩

theorem exists_closed_superset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : ∃ C, IsClosed C ∧ A ⊆ C := by
  exact ⟨closure A, isClosed_closure, subset_closure⟩

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : P1 A := by
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h] using this