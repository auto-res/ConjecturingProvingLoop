

theorem Topology.P1_closure_iff_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure A) ↔
      closure (interior (closure A)) = closure A := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.closed_P1_iff_closure_interior_eq_self
      (X := X) (A := closure A) hClosed)