

theorem closure_interior_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  -- First, we know `closure (interior A) ⊆ closure A`.
  have h_subset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_interior_subset_closure (A := A)
  -- Since `A` is closed, `closure A = A`, yielding the desired inclusion.
  simpa [hA_closed.closure_eq] using h_subset