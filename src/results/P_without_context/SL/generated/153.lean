

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P1]
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact Set.Subset.trans hP2 h₁