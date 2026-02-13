

theorem P123_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  exact ⟨Topology.P1_empty, Topology.P2_empty, Topology.P3_empty⟩