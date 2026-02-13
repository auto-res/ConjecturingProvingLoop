

theorem Topology.dense_closure_interior_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Dense (closure (interior A)) := by
  intro hDense
  have hEq : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  simpa [hEq] using dense_univ