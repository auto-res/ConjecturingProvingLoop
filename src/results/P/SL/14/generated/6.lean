

theorem Topology.interior_satisfies_P3 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  exact Topology.P2_implies_P3 (Topology.interior_satisfies_P2 A)