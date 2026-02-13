

theorem Topology.P3_iff_isClosed_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Topology.P3 (A := A) ↔ IsClosed A := by
  constructor
  · intro _; simpa using (isClosed_discrete _)
  · intro _; exact Topology.P3_of_discrete (A := A)