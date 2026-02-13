

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  exact Set.empty_subset _