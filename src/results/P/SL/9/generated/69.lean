

theorem Topology.P2_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (A : Set X) : Topology.P2 (A := A) := by
  have hA_open : IsOpen A := isOpen_discrete _
  exact Topology.P2_of_isOpen (A := A) hA_open