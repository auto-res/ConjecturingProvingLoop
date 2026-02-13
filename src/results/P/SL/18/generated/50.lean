

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  -- `interior A` is contained in `interior (closure A)` since `A ⊆ closure A`.
  have h : interior A ⊆ interior (closure A) := by
    apply interior_mono
    exact subset_closure
  -- Taking closures preserves inclusions.
  exact closure_mono h