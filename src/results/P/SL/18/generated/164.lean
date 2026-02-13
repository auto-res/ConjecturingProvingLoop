

theorem dense_iff_closure_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ closure (interior (closure (A : Set X))) = Set.univ := by
  constructor
  · intro hDense
    exact
      Topology.closure_interior_closure_eq_univ_of_dense (A := A) hDense
  · intro hEq
    exact
      Topology.dense_of_closure_interior_closure_eq_univ (A := A) hEq