

theorem Topology.closure_interior_closure_closure_eq_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure (A : Set X)))) =
      closure (interior (closure (A : Set X))) := by
  simpa [closure_closure]