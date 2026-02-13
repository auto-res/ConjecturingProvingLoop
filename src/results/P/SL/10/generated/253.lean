

theorem Topology.interior_subset_interior_union_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior B ⊆ interior (A ∪ B) := by
  exact interior_mono (Set.subset_union_right : B ⊆ A ∪ B)