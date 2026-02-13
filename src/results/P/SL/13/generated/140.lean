

theorem Topology.closure_interior_subset_closure_interior_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ⊆ closure (interior (A ∪ B)) := by
  -- `A` is contained in `A ∪ B`, so the same holds for their interiors.
  have h_subset : interior (A : Set X) ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  -- Taking closures preserves inclusions.
  exact closure_mono h_subset