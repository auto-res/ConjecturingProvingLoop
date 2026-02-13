

theorem interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  exact
    Set.Subset.trans
      (interior_closure_interior_subset_interior_closure (X := X) (A := A))
      interior_subset