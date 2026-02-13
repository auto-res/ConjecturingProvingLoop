

theorem Topology.P1_iff_isClosed_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Topology.P1 (A := A) ↔ IsClosed A := by
  constructor
  · intro _; simpa using (isClosed_discrete _)
  · intro _; exact Topology.P1_of_discrete (A := A)