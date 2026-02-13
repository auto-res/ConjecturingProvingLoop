

theorem P1_closure_iff_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (A : Set X)) ↔
      closure (interior (closure A)) = closure A := by
  simpa [closure_closure] using
    (Topology.P1_iff_closure_interior_eq_closure
      (A := closure (A : Set X)))