

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P1 A := by
  dsimp [Topology.P2, Topology.P1] at *
  exact subset_trans h interior_subset