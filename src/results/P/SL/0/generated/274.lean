

theorem interior_closure_eq_univ_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- Since `interior (closure A) = univ`, the inclusion
    -- `interior (closure A) ⊆ closure A` yields `univ ⊆ closure A`.
    have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      simpa [hInt] using
        (interior_subset :
          interior (closure (A : Set X)) ⊆ closure (A : Set X))
    -- Combine with the trivial inclusion `closure A ⊆ univ`.
    exact Set.Subset.antisymm (Set.subset_univ _) hSub
  · intro hCl
    -- If `closure A = univ`, its interior is also `univ`.
    simpa [hCl] using
      (interior_univ : interior (Set.univ : Set X) = (Set.univ : Set X))