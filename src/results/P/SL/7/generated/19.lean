

theorem Topology.P1_P2_P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [Topology.P1]
    intro x hx
    cases hx
  · dsimp [Topology.P2]
    intro x hx
    cases hx
  · dsimp [Topology.P3]
    intro x hx
    cases hx