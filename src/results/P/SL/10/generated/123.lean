

theorem Topology.closure_interior_closure_eq_univ_of_dense
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure A = (Set.univ : Set X)) :
    closure (interior (closure A)) = (Set.univ : Set X) := by
  simpa [h_dense, interior_univ, closure_univ]