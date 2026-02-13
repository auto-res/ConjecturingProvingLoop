

theorem Topology.interior_closure_closure_eq_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (A : Set X))) = interior (closure (A : Set X)) := by
  simpa [closure_closure]