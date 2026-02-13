

theorem closure_interInterior_subset_closure_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ B) ⊆ closure A := by
  -- The set `interior A ∩ B` is contained in `A`
  have h : interior A ∩ B ⊆ A := by
    intro x hx
    exact (interior_subset : interior A ⊆ A) hx.1
  -- Taking closures preserves inclusions
  exact closure_mono h