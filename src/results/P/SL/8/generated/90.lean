

theorem P3_closure_closure_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (closure A)) ↔ Topology.P3 (closure A) := by
  dsimp [Topology.P3]
  simpa [closure_closure]