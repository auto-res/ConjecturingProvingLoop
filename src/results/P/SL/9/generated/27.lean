

theorem Topology.P1_P2_P3_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (A : Set X) :
    Topology.P1 (A := A) ∧ Topology.P2 (A := A) ∧ Topology.P3 (A := A) := by
  have hA_open : IsOpen A := by
    simpa using isOpen_discrete A
  exact Topology.P1_P2_P3_of_isOpen (A := A) hA_open