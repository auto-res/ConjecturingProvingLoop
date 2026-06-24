

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (A := A)) : Topology.P1 (A := A) := by
  dsimp [Topology.P1, Topology.P2] at hA ⊢
  exact Set.Subset.trans hA interior_subset