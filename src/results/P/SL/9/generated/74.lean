

theorem Topology.P3_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (A : Set X) : Topology.P3 (A := A) := by
  exact (Topology.P1_P2_P3_of_discrete (A := A)).2.2