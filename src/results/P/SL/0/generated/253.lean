

theorem closure_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (∅ : Set X) ↔ (A : Set X) = ∅ := by
  constructor
  · intro h
    -- Since `A ⊆ closure A`, the hypothesis forces `A` to be empty.
    have hSub : (A : Set X) ⊆ (∅ : Set X) := by
      have : (A : Set X) ⊆ closure (A : Set X) := subset_closure
      simpa [h] using this
    exact Set.Subset.antisymm hSub (Set.empty_subset _)
  · intro h
    -- Replace `A` with `∅` in the left‐hand side and use `closure_empty`.
    simpa [h, closure_empty]