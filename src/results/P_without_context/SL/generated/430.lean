

theorem P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  dsimp [Topology.P2] at h
  dsimp [Topology.P1]
  intro x hx
  exact interior_subset (h hx)