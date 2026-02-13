

theorem Topology.interior_closure_interior_eq_univ_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    interior (closure (interior A)) = (Set.univ : Set X) := by
  simpa [h_dense, interior_univ]