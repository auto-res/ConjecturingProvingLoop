

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  dsimp [Topology.P2, Topology.P1]
  intro h x hx
  exact interior_subset (h hx)