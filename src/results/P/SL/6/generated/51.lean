

theorem empty_satisfies_all_Ps {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [Topology.P1]
    exact Set.empty_subset _
  · dsimp [Topology.P2]
    exact Set.empty_subset _
  · dsimp [Topology.P3]
    exact Set.empty_subset _