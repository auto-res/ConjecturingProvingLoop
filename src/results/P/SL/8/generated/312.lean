

theorem closure_interInterior_subset_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∩ interior B) ⊆ closure (A ∩ B) := by
  -- `interior A ∩ interior B` is contained in `A ∩ B`
  have h_subset : interior A ∩ interior B ⊆ A ∩ B := by
    intro x hx
    exact And.intro (interior_subset hx.1) (interior_subset hx.2)
  -- Taking closures preserves inclusions
  exact closure_mono h_subset