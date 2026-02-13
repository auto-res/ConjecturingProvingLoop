

theorem Topology.interior_union_frontier_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∪ frontier A ⊆ closure A := by
  intro x hx
  cases hx with
  | inl hx_int =>
      -- Points of `interior A` are, in particular, in `A`
      -- and hence lie in `closure A`.
      exact subset_closure (interior_subset hx_int)
  | inr hx_frontier =>
      -- By definition of the frontier, its points already
      -- belong to `closure A`.
      exact hx_frontier.1