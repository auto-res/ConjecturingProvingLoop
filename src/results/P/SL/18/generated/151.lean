

theorem closure_interior_subset_of_closed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    closure (interior (A : Set X)) ⊆ A := by
  have hSub :
      closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  simpa [hA_closed.closure_eq] using hSub