

theorem Topology.P2_closure_iff_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := closure A) ↔ Topology.P3 (A := closure A) := by
  have h_closed : IsClosed (closure A) := isClosed_closure
  simpa using
    (Topology.P2_iff_P3_of_isClosed (A := closure A) h_closed)