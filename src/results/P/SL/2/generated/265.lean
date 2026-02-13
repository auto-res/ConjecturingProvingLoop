

theorem Topology.closure_subset_closure_interior_of_frontier_subset
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    frontier (A : Set X) ⊆ closure (interior A) →
      closure (A : Set X) ⊆ closure (interior A) := by
  intro hFront x hxCl
  by_cases hxInt : x ∈ interior (A : Set X)
  · -- If `x` is already in `interior A`, the result is immediate.
    exact subset_closure hxInt
  · -- Otherwise, `x` lies in the frontier of `A`, hence in the target by `hFront`.
    have hxFront : x ∈ frontier (A : Set X) := by
      exact And.intro hxCl hxInt
    exact hFront hxFront