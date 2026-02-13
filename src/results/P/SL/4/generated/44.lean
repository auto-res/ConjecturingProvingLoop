

theorem interior_closure_interior_closure_interior_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    (interior_closure_interior_eq_interior_of_closed
      (X := X) (A := closure (interior A)) hClosed)