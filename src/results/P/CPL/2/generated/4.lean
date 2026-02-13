

theorem exists_dense_P2 {X : Type*} [TopologicalSpace X] [Nonempty X] : ∃ A : Set X, Dense A ∧ P2 (X := X) A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · simpa using dense_univ
  · simpa using P2_of_open (X := X) (A := Set.univ) isOpen_univ

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P2 (X := X) A := by
  classical
  unfold P2
  intro x hx
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [h.closure_eq, interior_univ] using this