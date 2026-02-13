

theorem interior_subset_interior_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A : Set X) ⊆ interior (A ∪ B : Set X) := by
  exact interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)