

theorem interior_closure_subset_interior_of_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} (h : closure A ⊆ B) :
    interior (closure A) ⊆ interior B := by
  exact interior_mono h