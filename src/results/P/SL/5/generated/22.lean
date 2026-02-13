

theorem closure_interior_idempotent_three {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
          simpa using closure_interior_idempotent_iter (X := X) (A := interior A)
    _ = closure (interior A) := by
          simpa using closure_interior_idempotent (X := X) (A := A)