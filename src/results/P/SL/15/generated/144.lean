

theorem P1_closure_iff_eq_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (closure A) ↔ closure A = closure (interior (closure A)) := by
  simpa [closure_closure] using
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := closure A))