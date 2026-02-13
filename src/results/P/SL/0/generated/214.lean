

theorem closure_interior_eq_empty_iff_interior_eq_empty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔
      interior (A : Set X) = (∅ : Set X) := by
  constructor
  · intro h
    have hSub : interior (A : Set X) ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure (interior (A : Set X)) := subset_closure hx
      simpa [h] using this
    exact Set.Subset.antisymm hSub (Set.empty_subset _)
  · intro h
    simpa [h, closure_empty]