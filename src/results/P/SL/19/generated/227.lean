

theorem Topology.interior_closure_subset_interior_union_frontier
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ interior A ∪ frontier A := by
  intro x hxIntClos
  by_cases hIntA : x ∈ interior A
  · exact Or.inl hIntA
  ·
    have hClosA : x ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hxIntClos
    have hFront : x ∈ frontier A := And.intro hClosA hIntA
    exact Or.inr hFront