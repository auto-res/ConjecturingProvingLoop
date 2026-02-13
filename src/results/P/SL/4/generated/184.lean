

theorem closure_union_closure_compl_univ {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure A ∪ closure (Aᶜ) = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · intro _x hx
    trivial
  · intro x _
    by_cases hA : x ∈ A
    · exact Or.inl (subset_closure hA)
    · have hAc : x ∈ Aᶜ := by
        simpa using hA
      exact Or.inr (subset_closure hAc)