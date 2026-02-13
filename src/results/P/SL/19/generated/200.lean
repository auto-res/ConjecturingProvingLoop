

theorem Topology.frontier_frontier_subset_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    frontier (frontier A) ⊆ frontier A := by
  intro x hx
  -- `frontier A` is closed, hence its closure is itself.
  have hClosed : IsClosed (frontier A) := Topology.isClosed_boundary (A := A)
  have hClosureEq : closure (frontier A) = frontier A := hClosed.closure_eq
  -- From `x ∈ frontier (frontier A)` we get `x ∈ closure (frontier A)`,
  -- which equals `frontier A`.
  have hxFront : x ∈ frontier A := by
    have : x ∈ closure (frontier A) := hx.1
    simpa [hClosureEq] using this
  exact hxFront