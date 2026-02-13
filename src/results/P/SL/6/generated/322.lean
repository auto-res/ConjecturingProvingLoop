

theorem closure_interior_closure_subset_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (interior (closure (A : Set X))) ⊆ A := by
  -- Since `A` is closed we have `closure A = A`.
  simpa [hA.closure_eq] using
    (closure_interior_subset_of_closed (A := A) hA)