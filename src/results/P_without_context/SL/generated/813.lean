

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A)) : Topology.P1 (A) := by
  dsimp [Topology.P1, Topology.P2] at *
  exact Set.Subset.trans h interior_subset