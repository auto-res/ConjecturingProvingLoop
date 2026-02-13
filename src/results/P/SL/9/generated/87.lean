

theorem Topology.closureInteriorClosureClosure_eq_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure A))) =
      closure (interior (closure A)) := by
  simpa [closure_closure]