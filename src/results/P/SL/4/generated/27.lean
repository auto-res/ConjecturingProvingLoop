

theorem interior_closure_interior_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure A))) = interior (closure A) := by
  have hClosed : IsClosed (closure A) := isClosed_closure
  simpa using
    (interior_closure_interior_eq_interior_of_closed
      (X := X) (A := closure A) hClosed)