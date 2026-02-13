

theorem closure_interior_subset_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : closure (interior A) ⊆ A := by
  -- `interior A` is contained in `A`
  have h_int : interior A ⊆ A := interior_subset
  -- Taking closures preserves inclusion
  have h_closure : closure (interior A) ⊆ closure A := closure_mono h_int
  -- Since `A` is closed, its closure is itself
  simpa [hA_closed.closure_eq] using h_closure