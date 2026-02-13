

theorem Topology.P2_closure_iff_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.closed_P2_iff_isOpen (X := X) (A := closure A) hClosed)