

theorem closure_interior_empty_iff_interior_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro hCl
    -- `interior A` is contained in its closure, which is `∅`.
    have hSub : interior A ⊆ (∅ : Set X) := by
      simpa [hCl] using
        (subset_closure : interior A ⊆ closure (interior A))
    exact Set.Subset.antisymm hSub (Set.empty_subset _)
  · intro hInt
    simpa [hInt, closure_empty]