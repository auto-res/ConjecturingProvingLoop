

theorem interior_closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
      simpa using
        (interior_closure_interior_idempotent (A := closure A))
    _ = interior (closure A) := by
      simpa using (interior_closure_idempotent (A := A))