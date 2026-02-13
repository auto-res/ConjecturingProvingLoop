

theorem Topology.closure_interior_subset_closure_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ⊆ closure (interior (A ∪ B)) := by
  -- Since `A ⊆ A ∪ B`, the corresponding interiors satisfy the same inclusion.
  have hInt : interior A ⊆ interior (A ∪ B) := by
    apply interior_mono
    intro x hx
    exact Or.inl hx
  -- Taking closures preserves inclusions.
  exact closure_mono hInt