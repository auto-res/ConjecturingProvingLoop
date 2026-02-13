

theorem Topology.closureInteriorClosure_eq_closureInterior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior (closure (A : Set X))) = closure (interior A) := by
  simpa [hA.closure_eq]