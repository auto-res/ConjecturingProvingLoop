

theorem isClosed_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (closure (A : Set X)))) := by
  simpa using
    (isClosed_closure :
      IsClosed (closure (interior (closure (A : Set X)))))