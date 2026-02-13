

theorem P3_closure_interior_iff_P2_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    Topology.P3 (closure (interior (A : Set X))) ↔
      Topology.P2 (closure (interior (A : Set X))) := by
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa using
    (Topology.P3_iff_P2_of_isClosed
      (A := closure (interior (A : Set X))) hClosed)