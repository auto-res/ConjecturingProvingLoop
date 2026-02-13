

theorem isClosed_of_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior (A : Set X)) = A) : IsClosed (A : Set X) := by
  -- The set `closure (interior A)` is always closed.
  have hClosed : IsClosed (closure (interior (A : Set X))) := isClosed_closure
  -- Rewrite using the given equality.
  simpa [h] using hClosed