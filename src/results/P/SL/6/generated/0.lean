

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hA
  dsimp [Topology.P2] at hA
  dsimp [Topology.P1]
  exact hA.trans interior_subset