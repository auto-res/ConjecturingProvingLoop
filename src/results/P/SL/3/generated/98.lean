

theorem interior_closure_eq_interior_of_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA : IsClosed (A : Set X)) :
    interior (closure (A : Set X)) = interior (A : Set X) := by
  simpa [hA.closure_eq]