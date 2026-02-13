

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (X := X) (∅ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  cases hx