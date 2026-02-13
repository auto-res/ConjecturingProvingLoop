

theorem closure_frontier_eq_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (frontier A) = frontier A := by
  have hClosed : IsClosed (frontier A) := frontier_isClosed (X := X) (A := A)
  simpa using hClosed.closure_eq