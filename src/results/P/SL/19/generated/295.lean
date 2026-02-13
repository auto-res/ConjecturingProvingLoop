

theorem Topology.subset_interior_union_frontier {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X) ⊆ interior A ∪ frontier A := by
  intro x hxA
  by_cases hInt : x ∈ interior A
  · exact Or.inl hInt
  ·
    have hClos : x ∈ closure A := subset_closure hxA
    exact Or.inr ⟨hClos, hInt⟩