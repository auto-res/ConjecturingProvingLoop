

theorem Topology.P2_iff_isOpen_of_discrete {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] {A : Set X} :
    Topology.P2 (A := A) ↔ IsOpen A := by
  -- In a discrete topology every set is open.
  have hOpen : IsOpen A := isOpen_discrete _
  constructor
  · intro _; exact hOpen
  · intro _; exact Topology.P2_of_discrete (A := A)