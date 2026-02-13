

theorem P2_closure_of_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hP3
  exact
    (Topology.P3_implies_P2_of_closed
        (A := closure (A : Set X)) isClosed_closure) hP3