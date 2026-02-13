

theorem Topology.closure_eq_union_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = A ∪ frontier A := by
  apply Set.Subset.antisymm
  · intro x hx_cl
    by_cases hA : x ∈ A
    · exact Or.inl hA
    ·
      have hx_not_int : x ∉ interior A := by
        intro hxInt
        have : x ∈ A := interior_subset hxInt
        exact hA this
      have hx_frontier : x ∈ frontier A := And.intro hx_cl hx_not_int
      exact Or.inr hx_frontier
  · intro x hx_union
    cases hx_union with
    | inl hxA =>
        exact subset_closure hxA
    | inr hxFrontier =>
        exact hxFrontier.1