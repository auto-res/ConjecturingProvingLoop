

theorem closure_subset_closure_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
  -- The set `A` is (trivially) contained in `A ∪ B`.
  have hSub : (A : Set X) ⊆ A ∪ B := by
    intro x hx
    exact Or.inl hx
  -- Taking closures preserves inclusions.
  exact closure_mono hSub