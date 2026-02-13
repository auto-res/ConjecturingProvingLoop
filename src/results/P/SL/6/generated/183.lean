

theorem closure_interior_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- `interior A` is contained in `A`, hence its closure is contained in `closure A`.
  have hSub : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Since `A` is closed, `closure A = A`.
  simpa [hA.closure_eq] using hSub