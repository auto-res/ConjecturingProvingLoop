

theorem Topology.P1_iff_isOpen_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Topology.P1 (A := A) ↔ IsOpen A := by
  constructor
  · intro _; exact isOpen_discrete _
  · intro hA_open; exact Topology.P1_of_isOpen (A := A) hA_open