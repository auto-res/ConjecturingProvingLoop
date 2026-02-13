

theorem Topology.all_P_empty {X : Type*} [TopologicalSpace X] :
    Topology.P1 (X := X) (∅ : Set X) ∧
      Topology.P2 (X := X) (∅ : Set X) ∧
        Topology.P3 (X := X) (∅ : Set X) := by
  exact
    ⟨Topology.P1_empty (X := X), Topology.P2_empty (X := X),
      Topology.P3_empty (X := X)⟩