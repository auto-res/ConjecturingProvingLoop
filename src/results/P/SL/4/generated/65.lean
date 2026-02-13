

theorem P2_iff_P3_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (closure A) ↔ Topology.P3 (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P2_iff_P3_of_closed (A := closure A) hClosed)