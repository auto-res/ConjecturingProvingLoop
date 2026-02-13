

theorem Topology.closure_closure_interior_eq_closure_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (closure (interior (A : Set X))) = closure (interior A) := by
  simpa [closure_closure]