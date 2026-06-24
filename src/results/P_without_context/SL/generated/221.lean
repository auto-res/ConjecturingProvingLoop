

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (A := A)) : Topology.P1 (A := A) := by
  dsimp [Topology.P2, Topology.P1] at *
  exact Set.Subset.trans hA interior_subset