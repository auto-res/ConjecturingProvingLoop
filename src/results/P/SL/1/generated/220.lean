

theorem Topology.closure_interior_subset_closure_interior_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  -- Since `B ⊆ A ∪ B`, the corresponding interiors satisfy the same inclusion.
  have hInt : interior B ⊆ interior (A ∪ B) := by
    apply interior_mono
    intro x hx
    exact Or.inr hx
  -- Taking closures preserves inclusions.
  exact closure_mono hInt