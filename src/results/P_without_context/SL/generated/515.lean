

theorem Topology.P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  dsimp [Topology.P1, Topology.P2] at *
  exact Set.Subset.trans h interior_subset