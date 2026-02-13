

theorem Topology.closureInteriorClosureClosure_eq_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure (A : Set X)))) =
      closure (interior (closure (A : Set X))) := by
  simpa [closure_closure]