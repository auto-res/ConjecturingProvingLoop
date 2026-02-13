

theorem Topology.closure_interior_subset_self_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) :
    closure (interior A) ⊆ A := by
  -- First, `interior A` is contained in `A`.
  have h₁ : interior A ⊆ A := interior_subset
  -- Taking closures preserves inclusions.
  have h₂ : closure (interior A) ⊆ closure A := closure_mono h₁
  -- Since `A` is closed, `closure A = A`; rewrite and conclude.
  simpa [hClosed.closure_eq] using h₂