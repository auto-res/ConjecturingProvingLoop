

theorem Topology.P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (∅ : Set X) := by
  dsimp [Topology.P1]
  simp