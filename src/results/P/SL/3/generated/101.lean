

theorem isClosed_of_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = A → IsClosed (A : Set X) := by
  intro hA
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  simpa [hA] using hClosed