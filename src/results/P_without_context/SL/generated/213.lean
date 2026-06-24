

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P1] at hP2
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) := by
    simpa using interior_subset
  exact subset_trans hP2 h₁