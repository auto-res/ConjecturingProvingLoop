

theorem P123_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧ Topology.P3 (Set.univ : Set X) := by
  exact ⟨Topology.P1_univ, Topology.P2_univ, Topology.P3_univ⟩