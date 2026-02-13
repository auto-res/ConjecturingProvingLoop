

theorem interior_diff_closure_eq {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (A \ closure (B : Set X)) = interior A \ closure B := by
  have hClosed : IsClosed (closure (B : Set X)) := isClosed_closure
  simpa using
    (interior_diff_of_closed (X := X) (A := A) (B := closure (B : Set X)) hClosed)