

theorem Topology.closure_interior_subset_self_union_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) ⊆ A ∪ frontier A := by
  intro x hx
  by_cases hInt : x ∈ interior A
  · exact Or.inl (interior_subset hInt)
  ·
    have hClosA : x ∈ closure A :=
      (Topology.closure_interior_subset_closure (A := A)) hx
    have hFront : x ∈ frontier A := And.intro hClosA hInt
    exact Or.inr hFront