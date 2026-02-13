

theorem Topology.P3_closure_iff_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.closed_P3_iff_isOpen (X := X) (A := closure A) hClosed)