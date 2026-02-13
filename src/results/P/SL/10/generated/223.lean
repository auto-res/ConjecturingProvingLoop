

theorem Topology.boundary_eq_diff_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    closure A \ interior A = A \ interior A := by
  simpa [hA.closure_eq]