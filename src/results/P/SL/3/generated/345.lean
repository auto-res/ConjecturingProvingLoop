

theorem closure_interior_subset_closure_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ⊆ closure (interior (A ∪ B)) := by
  -- First, note that `interior A ⊆ interior (A ∪ B)`.
  have hInt : interior (A : Set X) ⊆ interior (A ∪ B) := by
    apply interior_mono
    intro x hx
    exact Or.inl hx
  -- Taking closures preserves inclusions.
  exact closure_mono hInt