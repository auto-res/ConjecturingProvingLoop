

theorem Topology.P1_iff_P3_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Topology.P1 (A := A) ↔ Topology.P3 (A := A) := by
  constructor
  · intro _; exact Topology.P3_of_discrete (A := A)
  · intro _; exact Topology.P1_of_discrete (A := A)