

theorem frontier_frontier_subset_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    frontier (frontier A) ⊆ frontier A := by
  intro x hx
  -- `hx` provides `x ∈ closure (frontier A)`.
  have h_cl : x ∈ closure (frontier A) := hx.1
  -- Since `frontier A` is closed, its closure is itself.
  have h_closed : closure (frontier A) = frontier A := by
    have hIsClosed : IsClosed (frontier A) := frontier_isClosed (X := X) (A := A)
    simpa using hIsClosed.closure_eq
  -- Rewrite using the equality and finish.
  simpa [h_closed] using h_cl