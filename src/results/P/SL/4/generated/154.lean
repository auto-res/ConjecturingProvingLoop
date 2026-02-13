

theorem dense_closed_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → IsClosed A → A = (Set.univ : Set X) := by
  intro hDense hClosed
  have h : (closure A : Set X) = Set.univ := hDense.closure_eq
  simpa [hClosed.closure_eq] using h