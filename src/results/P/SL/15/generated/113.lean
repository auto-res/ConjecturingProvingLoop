

theorem closure_interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  -- First, note that `interior A` is contained in `interior (closure A)`.
  have h_int : interior A ⊆ interior (closure A) := by
    have h_subset : (A : Set X) ⊆ closure A := subset_closure
    exact interior_mono h_subset
  -- Taking closures preserves inclusions.
  exact closure_mono h_int