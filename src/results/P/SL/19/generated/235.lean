

theorem Topology.interior_closure_union_frontier_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure A) ∪ frontier A = closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases hx with
    | inl hInt =>
        exact (interior_subset : interior (closure A) ⊆ closure A) hInt
    | inr hFront =>
        exact (Topology.frontier_subset_closure (A := A)) hFront
  · exact Topology.closure_subset_interior_closure_union_frontier (A := A)