

theorem isClosed_of_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = A) : IsClosed A := by
  simpa [h] using (isClosed_closure : IsClosed (closure (interior A)))