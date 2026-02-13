

theorem P2_implies_P3_of_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 (interior A) := by
  intro _
  exact Topology.open_satisfies_P3 (A := interior A) isOpen_interior