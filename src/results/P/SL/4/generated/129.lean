

theorem isClosed_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (closure A))) := by
  simpa using
    (isClosed_closure : IsClosed (closure (interior (closure A))))