

theorem Topology.dense_isClosed_implies_univ {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → IsClosed A → (A : Set X) = (Set.univ : Set X) := by
  intro hDense hClosed
  simpa [hClosed.closure_eq] using hDense.closure_eq