

theorem Topology.interior_union_frontier_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ∪ frontier A = closure A := by
  ext x
  constructor
  · intro h
    cases h with
    | inl hInt =>
        exact (Topology.interior_subset_closure (A := A)) hInt
    | inr hFront =>
        exact hFront.1
  · intro hClos
    by_cases hInt : x ∈ interior A
    · exact Or.inl hInt
    ·
      have hFront : x ∈ frontier A := And.intro hClos hInt
      exact Or.inr hFront