

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 A) : Topology.P1 A := by
  dsimp [Topology.P1, Topology.P2] at *
  intro x hx
  exact interior_subset (h hx)