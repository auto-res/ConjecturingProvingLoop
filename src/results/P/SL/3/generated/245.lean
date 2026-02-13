

theorem boundary_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    closure (A : Set X) \ interior (A : Set X) = A \ interior (A : Set X) := by
  simpa [hA.closure_eq]