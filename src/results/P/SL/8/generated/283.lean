

theorem interior_closure_interior_inter_subset_interior_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A ∩ interior B)) ⊆
      interior (closure (A ∩ B)) := by
  -- First, note that `interior A ∩ interior B ⊆ A ∩ B`.
  have h_subset : interior A ∩ interior B ⊆ A ∩ B := by
    intro x hx
    exact And.intro (interior_subset hx.1) (interior_subset hx.2)
  -- Taking closures preserves inclusions.
  have h_closure :
      closure (interior A ∩ interior B) ⊆ closure (A ∩ B) :=
    closure_mono h_subset
  -- Applying `interior_mono` yields the desired inclusion.
  exact interior_mono h_closure