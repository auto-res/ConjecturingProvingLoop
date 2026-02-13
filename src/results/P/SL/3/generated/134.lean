

theorem P1_iff_P1_closure_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 A ↔ Topology.P1 (closure (A : Set X)) := by
  simpa [hA_closed.closure_eq]