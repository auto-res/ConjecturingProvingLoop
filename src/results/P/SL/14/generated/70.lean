

theorem Topology.interiorClosureClosure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]