

theorem closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  -- First, identify the key equality for interiors using the closedness of `closure A`.
  have hInt :
      interior (closure (interior (closure A))) = interior (closure A) := by
    have hClosed : IsClosed (closure A) := isClosed_closure
    simpa using
      (interior_closure_interior_eq_interior_of_closed
        (X := X) (A := closure A) hClosed)
  -- Taking closures of both sides preserves equality.
  simpa [hInt]