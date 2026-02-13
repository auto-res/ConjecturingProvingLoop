

theorem Topology.empty_satisfies_P1_P2_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P1, Topology.P2, Topology.P3]
  simp