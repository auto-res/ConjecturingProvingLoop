

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 A) : Topology.P3 A := by
  dsimp [Topology.P2, Topology.P3] at hA ⊢
  exact subset_trans hA (interior_mono (closure_mono interior_subset))