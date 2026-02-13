

theorem closure_interior_subset_closure_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure (interior A))) := by
  -- First, show `interior A ⊆ interior (closure (interior A))`.
  have hInt : interior A ⊆ interior (closure (interior A)) := by
    have h' : interior (interior A) ⊆ interior (closure (interior A)) := by
      -- `interior` is monotone with respect to set inclusion.
      exact
        interior_mono
          (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    simpa [interior_interior] using h'
  -- Taking closures preserves inclusions.
  exact closure_mono hInt