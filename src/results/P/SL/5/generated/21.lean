

theorem interior_closure_idempotent_three {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  have h1 := interior_closure_idempotent_iter (X := X) (A := closure A)
  have h2 := interior_closure_idempotent (X := X) (A := A)
  calc
    interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
          simpa using h1
    _ = interior (closure A) := by
          simpa using h2