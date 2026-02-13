

theorem isClosed_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = A) : IsClosed (A : Set X) := by
  simpa [h] using (isClosed_closure : IsClosed (closure (A : Set X)))