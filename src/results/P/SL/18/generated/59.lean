

theorem P123_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (∅ : Set X) ∧ Topology.P2 (∅ : Set X) ∧ Topology.P3 (∅ : Set X) := by
  exact ⟨Topology.P1_empty (X := X), Topology.P2_empty (X := X), Topology.P3_empty (X := X)⟩