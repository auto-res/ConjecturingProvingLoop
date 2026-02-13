

theorem isClosed_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior (A : Set X))) := by
  -- The closure of any set is closed.
  simpa using
    (isClosed_closure : IsClosed (closure (interior (A : Set X))))