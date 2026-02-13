

theorem closure_subset_closure_union_three {X : Type*} [TopologicalSpace X]
    {A B C : Set X} :
    closure (A : Set X) ⊆ closure (A ∪ B ∪ C : Set X) := by
  -- The set `A` is contained in `A ∪ B ∪ C`.
  have hSub : (A : Set X) ⊆ A ∪ B ∪ C := by
    intro x hx
    exact Or.inl (Or.inl hx)
  -- Taking closures preserves the inclusion.
  exact closure_mono hSub