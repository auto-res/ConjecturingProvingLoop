

theorem closure_interInterior_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure B := by
  -- Since `interior B ⊆ B`, the set `A ∩ interior B` is contained in `B`.
  have h : A ∩ interior B ⊆ B := by
    intro x hx
    exact (interior_subset : interior B ⊆ B) hx.2
  -- Taking closures preserves inclusions.
  exact closure_mono h