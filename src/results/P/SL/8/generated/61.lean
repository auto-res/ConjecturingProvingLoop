

theorem empty_P1_P2_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  constructor
  · dsimp [Topology.P1]; simp
  · constructor
    · dsimp [Topology.P2]; simp
    · dsimp [Topology.P3]; simp