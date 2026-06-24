

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P3] at hP2 ⊢
  have h_mono : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h₁ : closure (interior A) ⊆ closure A := by
      have h₀ : interior A ⊆ A := interior_subset
      exact closure_mono h₀
    exact interior_mono h₁
  exact Set.Subset.trans hP2 h_mono