

theorem Topology.P1_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    {A : Set X} : Topology.P1 A := by
  -- Every subset of a discrete space is open.
  have hOpen : IsOpen A := isOpen_discrete _
  -- All open sets satisfy `P1`.
  exact Topology.P1_of_isOpen (A := A) hOpen