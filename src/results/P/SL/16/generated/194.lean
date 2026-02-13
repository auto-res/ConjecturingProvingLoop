

theorem Topology.closure_interior_closure_eq_closure_interior_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hClosed : IsClosed A) :
    closure (interior (closure A)) = closure (interior A) := by
  simpa [hClosed.closure_eq]