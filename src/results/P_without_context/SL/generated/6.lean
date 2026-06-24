

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hA
  dsimp [Topology.P1, Topology.P2] at *
  exact subset_trans hA interior_subset