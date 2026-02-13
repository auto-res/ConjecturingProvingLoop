

theorem P2_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (closure A)) ↔ Topology.P2 (closure A) := by
  dsimp [Topology.P2]
  simpa [closure_closure]