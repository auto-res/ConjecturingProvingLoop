

theorem interior_subset_interior_union_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A : Set X) ⊆ interior (A ∪ B) := by
  apply interior_mono
  intro x hx
  exact Or.inl hx