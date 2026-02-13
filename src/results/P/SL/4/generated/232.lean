

theorem closure_eq_union_frontier {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A = A ∪ frontier A := by
  ext x
  constructor
  · intro hx
    by_cases hA : x ∈ A
    · exact Or.inl hA
    · -- `x` is not in `A`, so it must lie in the frontier.
      have h_not_int : x ∉ interior A := by
        intro hxInt
        exact hA (interior_subset hxInt)
      have h_front : x ∈ frontier A := And.intro hx h_not_int
      exact Or.inr h_front
  · intro h
    cases h with
    | inl hA =>
        exact subset_closure hA
    | inr hFront =>
        exact hFront.1