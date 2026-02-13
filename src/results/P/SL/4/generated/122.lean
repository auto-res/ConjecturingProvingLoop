

theorem P3_closure_iff_isOpen_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P3 (closure A) ↔ IsOpen (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P3_closed_iff_isOpen (A := closure A) hClosed)