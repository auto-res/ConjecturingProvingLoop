

theorem P1_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) := by
  dsimp [Topology.P1]
  exact Set.empty_subset _