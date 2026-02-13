

theorem interior_subset_interior_union_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (B : Set X) ⊆ interior (A ∪ B : Set X) := by
  exact interior_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)