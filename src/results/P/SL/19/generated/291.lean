

theorem Topology.interior_union_interior_compl_union_frontier_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ∪ interior (Aᶜ) ∪ frontier A = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    by_cases h : x ∈ interior A ∪ interior (Aᶜ)
    · exact Or.inl h
    ·
      have hFront :
          frontier A = (interior A ∪ interior (Aᶜ))ᶜ :=
        Topology.frontier_eq_compl_interior_union_interior_compl (A := A)
      have hxFront : x ∈ frontier A := by
        have hxComp : x ∈ (interior A ∪ interior (Aᶜ))ᶜ := by
          simpa [Set.mem_compl] using h
        simpa [hFront] using hxComp
      exact Or.inr hxFront