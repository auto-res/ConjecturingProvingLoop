

theorem Topology.P1_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P1 (closure (A : Set X)) := by
  intro hP2cl
  have hClosed : IsClosed (closure (A : Set X)) := isClosed_closure
  exact Topology.P1_of_P2_closed (A := closure (A : Set X)) hClosed hP2cl