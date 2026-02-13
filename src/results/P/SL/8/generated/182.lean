

theorem interior_closure_eq_univ_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔
      closure A = (Set.univ : Set X) := by
  constructor
  · intro hInt
    have h_subset : (Set.univ : Set X) ⊆ closure A := by
      have h_sub : interior (closure A) ⊆ closure A := interior_subset
      simpa [hInt] using h_sub
    exact Set.Subset.antisymm (Set.subset_univ _) h_subset
  · intro hCl
    have : interior (closure A) = interior (Set.univ : Set X) := by
      simpa [hCl]
    simpa [interior_univ] using this