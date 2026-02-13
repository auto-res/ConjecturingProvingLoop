

theorem interior_closure_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    interior (closure A) ⊆ A := by
  -- Since `A` is closed, `closure A = A`.
  simpa [hA_closed.closure_eq] using
    (interior_subset : interior (closure A) ⊆ closure A)