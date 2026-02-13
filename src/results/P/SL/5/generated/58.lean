

theorem closure_interior_subset_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- `interior A` is obviously contained in `A`.
  have h_subset : (interior (A : Set X) : Set X) ⊆ A := interior_subset
  -- Taking closures preserves inclusions.
  have h_closure_subset : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono h_subset
  -- Since `A` is closed, its closure is itself.
  simpa [hA.closure_eq] using h_closure_subset