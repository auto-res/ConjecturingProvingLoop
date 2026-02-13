

theorem Topology.closure_interior_subset_closure_interior_union_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior B) ⊆ closure (interior (A ∪ B)) := by
  have h_subset : interior B ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_right : B ⊆ A ∪ B)
  exact closure_mono h_subset