

theorem P2_closure_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (closure (A : Set X))) ↔
      Topology.P2 (closure (A : Set X)) := by
  simpa [closure_closure]