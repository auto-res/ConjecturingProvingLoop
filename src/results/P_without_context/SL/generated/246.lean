

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P3 (A := A) := by
  intro hP2
  unfold Topology.P2 at hP2
  unfold Topology.P3
  have h₁ : interior (closure (interior A)) ⊆ interior (closure A) := by
    have h₀ : closure (interior A) ⊆ closure A := by
      have : interior A ⊆ A := interior_subset
      exact closure_mono this
    exact interior_mono h₀
  exact subset_trans hP2 h₁