

theorem P3_closure_iff_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) ↔ interior (closure A) = closure A := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_interior_eq (X := X) (A := closure A) h_closed)