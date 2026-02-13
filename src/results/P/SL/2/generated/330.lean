

theorem Topology.closure_eq_self_union_frontier {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (A : Set X) = (A : Set X) ∪ frontier (A : Set X) := by
  ext x
  constructor
  · intro hxCl
    by_cases hxA : x ∈ (A : Set X)
    · exact Or.inl hxA
    ·
      -- Since `x ∉ A` and `x ∈ closure A`, we have `x ∈ frontier A`.
      have hxFront : x ∈ frontier (A : Set X) := by
        have hxNotInt : x ∉ interior (A : Set X) := by
          intro hxInt
          exact hxA (interior_subset hxInt)
        exact And.intro hxCl hxNotInt
      exact Or.inr hxFront
  · intro h
    cases h with
    | inl hxA =>
        exact subset_closure hxA
    | inr hxFront =>
        exact hxFront.1