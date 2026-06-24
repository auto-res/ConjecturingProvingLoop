

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A := by
  intro h
  dsimp [Topology.P2, Topology.P3] at h ⊢
  exact
    Set.Subset.trans h
      (interior_mono
        (closure_mono interior_subset))