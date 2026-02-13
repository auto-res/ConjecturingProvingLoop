

theorem P3_implies_P2_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → Topology.P2 (interior A) := by
  intro _
  exact Topology.open_satisfies_P2 (A := interior A) isOpen_interior