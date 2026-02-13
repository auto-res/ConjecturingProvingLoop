

theorem P3_empty {X : Type*} [TopologicalSpace X] :
    Topology.P3 (∅ : Set X) := by
  dsimp [Topology.P3]
  simpa using
    (Set.empty_subset : (∅ : Set X) ⊆ interior (closure (∅ : Set X)))