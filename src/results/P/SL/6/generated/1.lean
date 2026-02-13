

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hA
  dsimp [Topology.P2, Topology.P3] at *
  exact hA.trans (interior_mono (closure_mono interior_subset))