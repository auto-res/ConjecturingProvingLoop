

theorem Topology.P_properties_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] {A : Set X} :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.P1_of_discrete (A := A),
      ⟨Topology.P2_of_discrete (A := A),
        Topology.P3_of_discrete (A := A)⟩⟩