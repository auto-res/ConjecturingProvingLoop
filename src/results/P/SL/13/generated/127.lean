

theorem Topology.interior_closure_eq_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = interior A := by
  simpa [hA_closed.closure_eq]