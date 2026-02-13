

theorem Topology.P2_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (closure (A : Set X))) ↔
      Topology.P2 (X := X) (closure A) := by
  simpa [closure_closure]