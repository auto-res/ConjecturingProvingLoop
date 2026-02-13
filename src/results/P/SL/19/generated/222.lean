

theorem Topology.closure_subset_interior_closure_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A ⊆ interior (closure A) ∪ frontier A := by
  intro x hxClos
  by_cases hInt : x ∈ interior (closure A)
  · exact Or.inl hInt
  ·
    have hNotIntA : x ∉ interior A := by
      intro hIntA
      have : x ∈ interior (closure A) :=
        (Topology.interior_subset_interior_closure (A := A)) hIntA
      exact hInt this
    have hxFront : x ∈ frontier A := And.intro hxClos hNotIntA
    exact Or.inr hxFront