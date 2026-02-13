

theorem Topology.empty_is_P1_and_P2_and_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (A := (∅ : Set X)) ∧
      Topology.P2 (A := (∅ : Set X)) ∧
      Topology.P3 (A := (∅ : Set X)) := by
  constructor
  · dsimp [Topology.P1]
    intro x hx
    cases hx
  · constructor
    · dsimp [Topology.P2]
      intro x hx
      cases hx
    · dsimp [Topology.P3]
      intro x hx
      cases hx