

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P1] at hP2 ⊢
  exact Set.Subset.trans hP2 interior_subset