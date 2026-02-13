

theorem Topology.closure_interior_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → closure (interior A) = (Set.univ : Set X) := by
  intro hDenseInt
  simpa using hDenseInt.closure_eq