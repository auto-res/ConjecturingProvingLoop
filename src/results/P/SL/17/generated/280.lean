

theorem Topology.closure_interior_subset_closure_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A) ⊆ closure (interior (A ∪ B)) := by
  have h_sub : interior A ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_left : A ⊆ A ∪ B)
  exact closure_mono h_sub