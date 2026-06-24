

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 A :=
by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at *
  exact
    subset_trans hP2
      (interior_mono
        (closure_mono
          (interior_subset : interior A ⊆ A)))