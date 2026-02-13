

theorem interior_closure_interior_double_idempotent {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) =
      interior (closure (interior (A : Set X))) := by
  calc
    interior (closure (interior (closure (interior (closure (interior (A : Set X)))))))
        = interior (closure (interior (closure (interior (A : Set X))))) := by
          simpa using
            interior_closure_interior_idempotent
              (A := closure (interior (A : Set X)))
    _ = interior (closure (interior (A : Set X))) := by
          simpa using
            interior_closure_interior_idempotent (A := A)