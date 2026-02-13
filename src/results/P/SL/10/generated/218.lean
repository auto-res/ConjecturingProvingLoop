

theorem Topology.closure_interior_subset_closure_interior_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ⊆ closure (interior (A ∪ B)) := by
  -- First, note the inclusion `A ⊆ A ∪ B`, and pass to interiors.
  have h : interior A ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
  -- Taking closures preserves set inclusion.
  exact closure_mono h