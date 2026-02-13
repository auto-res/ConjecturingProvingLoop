

theorem closure_subset_closure_union_right {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (B : Set X) ⊆ closure (A ∪ B : Set X) := by
  -- `B` is contained in `A ∪ B`.
  have hSub : (B : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inr hx
  -- Taking closures preserves inclusions.
  exact closure_mono hSub