

theorem Topology.boundary_eq_univ_diff_interior_of_dense {X : Type*}
    [TopologicalSpace X] {A : Set X} (hDense : Dense (A : Set X)) :
    closure (A : Set X) \ interior A = (Set.univ : Set X) \ interior A := by
  simpa [hDense.closure_eq]