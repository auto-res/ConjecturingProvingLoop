

theorem closure_interior_subset_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    closure (interior A) ⊆ A := by
  -- `interior A` is contained in `A`
  have hInt : interior A ⊆ A := interior_subset
  -- Taking closures preserves inclusions
  have hClos : closure (interior A) ⊆ closure A := closure_mono hInt
  -- Since `A` is closed, `closure A = A`
  simpa [hA_closed.closure_eq] using hClos