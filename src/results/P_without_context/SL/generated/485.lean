

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hA
  dsimp [Topology.P2, Topology.P1] at *
  exact subset_trans hA interior_subset