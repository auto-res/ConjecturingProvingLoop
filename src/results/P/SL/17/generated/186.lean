

theorem Topology.P2_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    {A : Set X} : Topology.P2 A := by
  -- In a discrete topology every set is open.
  have hOpen : IsOpen A := isOpen_discrete _
  -- `P2` holds for every open set.
  exact Topology.P2_of_isOpen (A := A) hOpen