

theorem closure_frontier_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier A) ⊆ closure A := by
  -- `frontier A` is closed, hence its closure equals itself.
  have h_eq : closure (frontier A) = frontier A := by
    have hClosed : IsClosed (frontier A) := frontier_isClosed (X := X) (A := A)
    simpa using hClosed.closure_eq
  -- The frontier of `A` is contained in `closure A`.
  have h_subset : frontier A ⊆ closure A :=
    frontier_subset_closure (X := X) (A := A)
  simpa [h_eq] using h_subset