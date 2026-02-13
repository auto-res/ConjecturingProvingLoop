

theorem closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔ interior (A : Set X) = ∅ := by
  constructor
  · intro h
    -- Since `interior A ⊆ closure (interior A)`, the hypothesis forces `interior A = ∅`.
    have hSub : interior (A : Set X) ⊆ (∅ : Set X) := by
      have : interior (A : Set X) ⊆ closure (interior (A : Set X)) :=
        subset_closure
      simpa [h] using this
    exact
      (Set.Subset.antisymm hSub (Set.empty_subset _))
  · intro h
    simpa [h, closure_empty]