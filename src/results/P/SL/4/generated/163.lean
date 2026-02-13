

theorem interior_closure_subset_interior_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A) ⊆ interior (closure (A ∪ B)) := by
  exact
    interior_mono
      (closure_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B))