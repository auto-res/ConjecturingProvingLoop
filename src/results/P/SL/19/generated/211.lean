

theorem Topology.closure_eq_self_union_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A = A ∪ frontier A := by
  ext x
  constructor
  · intro hxClos
    by_cases hA : x ∈ A
    · exact Or.inl hA
    ·
      have hxNotInt : x ∉ interior A := by
        intro hxInt
        exact hA (interior_subset hxInt)
      have hxFront : x ∈ frontier A := And.intro hxClos hxNotInt
      exact Or.inr hxFront
  · intro hx
    cases hx with
    | inl hA      => exact subset_closure hA
    | inr hFront  => exact hFront.1