

theorem Topology.closed_dense_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → Dense A → (A : Set X) = Set.univ := by
  intro hClosed hDense
  have h1 : closure A = A := hClosed.closure_eq
  have h2 : closure A = (Set.univ : Set X) := hDense.closure_eq
  simpa [h1] using h2