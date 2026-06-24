

theorem Topology.P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  dsimp [Topology.P1]
  dsimp [Topology.P2] at h
  exact Set.Subset.trans h (by
    simpa using interior_subset)