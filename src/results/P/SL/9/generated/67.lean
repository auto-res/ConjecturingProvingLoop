

theorem Topology.P1_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) :
    Topology.P1 (A := A) := by
  exact (Topology.P1_P2_P3_of_discrete (A := A)).1