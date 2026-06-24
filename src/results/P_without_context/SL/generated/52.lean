

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 (A : Set X) := by
  intro hA
  dsimp [Topology.P1, Topology.P2] at hA ⊢
  exact subset_trans hA interior_subset