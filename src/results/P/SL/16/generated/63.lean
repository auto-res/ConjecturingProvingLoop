

theorem Topology.interior_closure_eq_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hClosed : IsClosed A) :
    interior (closure A) = interior A := by
  simpa [hClosed.closure_eq]