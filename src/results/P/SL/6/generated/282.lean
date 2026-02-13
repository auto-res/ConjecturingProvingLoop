

theorem interior_closure_eq_univ_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      have hIntSub : interior (closure (A : Set X)) ⊆ closure A :=
        interior_subset
      simpa [hInt] using hIntSub
    have hSup : closure (A : Set X) ⊆ (Set.univ : Set X) :=
      Set.subset_univ _
    exact Set.Subset.antisymm hSup hSub
  · intro hClos
    simpa [hClos, interior_univ]