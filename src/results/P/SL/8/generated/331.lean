

theorem interior_closure_interInterior_subset_interior_closure_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A ∩ B)) ⊆ interior (closure B) := by
  -- `interior A ∩ B` is contained in `B`.
  have h_subset : interior A ∩ B ⊆ B := by
    intro x hx
    exact hx.2
  -- Taking closures preserves inclusions.
  have h_closure : closure (interior A ∩ B) ⊆ closure B :=
    closure_mono h_subset
  -- Applying `interior_mono` yields the desired inclusion.
  exact interior_mono h_closure