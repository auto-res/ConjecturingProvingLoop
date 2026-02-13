

theorem interior_closure_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) ⊆ A := by
  have h : interior (closure (A : Set X)) ⊆ closure A := interior_subset
  simpa [hA.closure_eq] using h