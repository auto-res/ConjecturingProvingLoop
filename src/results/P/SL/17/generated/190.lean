

theorem Topology.P3_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    {A : Set X} : Topology.P3 A := by
  have hOpen : IsOpen A := isOpen_discrete _
  exact Topology.P3_of_isOpen (A := A) hOpen