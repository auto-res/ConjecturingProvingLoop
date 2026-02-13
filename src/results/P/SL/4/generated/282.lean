

theorem interior_union_frontier_eq_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior A ∪ frontier A = closure A := by
  ext x
  constructor
  · intro hx
    cases hx with
    | inl hxInt =>
        -- Points of `interior A` certainly lie in `closure A`.
        have hxA : x ∈ A := interior_subset hxInt
        exact subset_closure hxA
    | inr hxFront =>
        -- The frontier is contained in the closure.
        exact hxFront.1
  · intro hxCl
    -- Case split on whether `x` already lies in `interior A`.
    by_cases hxInt : x ∈ interior A
    · exact Or.inl hxInt
    · -- Otherwise, `x` belongs to the frontier.
      have hxFront : x ∈ frontier A := And.intro hxCl hxInt
      exact Or.inr hxFront