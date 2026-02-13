

theorem closure_interInterior_subset_closureInterior_and_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure (interior A) ∩ closure B := by
  intro x hx
  have hx₁ : x ∈ closure (interior A) := by
    -- `interior A ∩ B` is contained in `interior A`
    have h_subset : interior A ∩ B ⊆ interior A := by
      intro y hy
      exact hy.1
    exact (closure_mono h_subset) hx
  have hx₂ : x ∈ closure B := by
    -- `interior A ∩ B` is contained in `B`
    have h_subset : interior A ∩ B ⊆ B := by
      intro y hy
      exact hy.2
    exact (closure_mono h_subset) hx
  exact And.intro hx₁ hx₂