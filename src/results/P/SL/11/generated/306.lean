

theorem closure_union_interior_subset_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∪ interior B) ⊆ closure (A ∪ B) := by
  -- The subset relation on the underlying sets
  have hSub : (A ∪ interior B : Set X) ⊆ A ∪ B := by
    intro x hx
    cases hx with
    | inl hA   => exact Or.inl hA
    | inr hInt => exact Or.inr ((interior_subset : interior B ⊆ B) hInt)
  -- Taking closures preserves inclusions
  exact closure_mono hSub