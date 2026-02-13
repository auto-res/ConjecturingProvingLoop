

theorem Topology.closure_union_closure_compl_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · intro _ _
    exact Set.mem_univ _
  · intro x _
    by_cases hA : x ∈ A
    · exact Or.inl (subset_closure hA)
    · have : x ∈ Aᶜ := hA
      exact Or.inr (subset_closure this)