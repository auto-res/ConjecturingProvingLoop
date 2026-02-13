

theorem Topology.boundary_eq_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    closure (A : Set X) \ interior A = A \ interior A := by
  simpa [hA.closure_eq]