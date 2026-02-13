

theorem closure_interInterior_subset_closureInterior_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure (interior A) := by
  -- `interior A ∩ B` is contained in `interior A`
  have h : interior A ∩ B ⊆ interior A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions
  exact closure_mono h