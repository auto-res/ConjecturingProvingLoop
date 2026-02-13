

theorem Topology.boundary_eq_diff_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior A = (A : Set X) \ interior A := by
  simpa [hA_closed.closure_eq]