

theorem p2_imp_p1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hA
  dsimp [Topology.P1, Topology.P2] at *
  exact Set.Subset.trans hA interior_subset