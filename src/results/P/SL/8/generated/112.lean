

theorem closureInterior_subset_closureInterior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ⊆ closure (interior (A ∪ B)) := by
  have hInt : interior A ⊆ interior (A ∪ B) := by
    have hSub : A ⊆ A ∪ B := by
      intro x hx; exact Or.inl hx
    exact interior_mono hSub
  exact closure_mono hInt