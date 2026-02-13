

theorem boundary_closed {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (A : Set X) \ interior (A : Set X)) := by
  simpa using
    (isClosed_closure_diff_interior (A := A))