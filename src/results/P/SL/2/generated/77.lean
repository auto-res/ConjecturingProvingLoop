

theorem Topology.P3_closure_implies_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hP3
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  exact
    Topology.isClosed_P3_implies_P2 (A := closure (A : Set X)) hClosed hP3