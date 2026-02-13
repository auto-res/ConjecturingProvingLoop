

theorem empty_has_all_P {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  have hP1 : Topology.P1 (∅ : Set X) := by
    dsimp [Topology.P1]
    exact Set.empty_subset _
  have hP2 : Topology.P2 (∅ : Set X) := by
    dsimp [Topology.P2]
    exact Set.empty_subset _
  have hP3 : Topology.P3 (∅ : Set X) := by
    dsimp [Topology.P3]
    exact Set.empty_subset _
  exact ⟨hP1, hP2, hP3⟩