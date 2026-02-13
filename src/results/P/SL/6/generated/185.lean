

theorem closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔ interior A = ∅ := by
  constructor
  · intro h
    have hSub : interior (A : Set X) ⊆ (∅ : Set X) := by
      have : interior (A : Set X) ⊆ closure (interior A) := subset_closure
      simpa [h] using this
    exact Set.Subset.antisymm hSub (Set.empty_subset _)
  · intro h
    simpa [h, closure_empty]