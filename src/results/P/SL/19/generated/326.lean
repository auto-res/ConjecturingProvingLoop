

theorem Topology.frontier_interior_subset_closure_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (interior A) ⊆ closure (frontier A) := by
  intro x hx
  -- First, move from the frontier of `interior A` to the frontier of `A`.
  have hFrontA : x ∈ frontier A :=
    (Topology.frontier_interior_subset_frontier (A := A)) hx
  -- Then use the fact that every set is contained in the closure of itself.
  exact (subset_closure : frontier A ⊆ closure (frontier A)) hFrontA