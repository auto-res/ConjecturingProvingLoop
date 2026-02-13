

theorem closure_union_compl_eq_univ {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ∪ closure ((A : Set X)ᶜ) = (Set.univ : Set X) := by
  classical
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases hA : x ∈ (A : Set X)
    · exact Or.inl (subset_closure hA)
    · have hAc : x ∈ ((A : Set X)ᶜ) := by
        simpa using hA
      exact Or.inr (subset_closure hAc)