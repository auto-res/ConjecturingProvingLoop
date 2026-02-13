

theorem Topology.closureInteriorClosure_eq_closureInterior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    closure (interior (closure A)) = closure (interior A) := by
  simpa [hA_closed.closure_eq]