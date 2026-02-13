

theorem interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (interior A) := by
  exact (subset_closure : interior (A : Set X) ⊆ closure (interior A))