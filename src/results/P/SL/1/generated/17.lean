

theorem P2_empty {X : Type*} [TopologicalSpace X] :
    Topology.P2 (∅ : Set X) := by
  dsimp [Topology.P2]
  simpa using
    (Set.empty_subset :
      (∅ : Set X) ⊆ interior (closure (interior (∅ : Set X))))