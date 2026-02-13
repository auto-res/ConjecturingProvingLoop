

theorem P3_closure_iff_P2_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (closure (A : Set X)) ↔ Topology.P2 (closure (A : Set X)) := by
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  simpa using
    (Topology.P3_iff_P2_of_isClosed
      (A := closure (A : Set X)) hClosed)