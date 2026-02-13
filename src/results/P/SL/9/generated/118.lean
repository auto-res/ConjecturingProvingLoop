

theorem Topology.closure_closureInterior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure (interior A)) = closure (interior A) := by
  simpa [closure_closure]