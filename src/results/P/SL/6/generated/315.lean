

theorem closure_interior_closure_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (interior (closure (A : Set X))) ⊆ A := by
  -- Since `A` is closed, its closure is itself.
  have hEq : closure (A : Set X) = A := hA.closure_eq
  -- `interior (closure A)` is contained in `closure A`, hence in `A`.
  have hSub : interior (closure (A : Set X)) ⊆ A := by
    simpa [hEq] using
      (interior_subset : interior (closure (A : Set X)) ⊆ closure A)
  -- Taking closures preserves inclusions; rewrite using `hEq`.
  simpa [hEq, closure_closure] using (closure_mono hSub)