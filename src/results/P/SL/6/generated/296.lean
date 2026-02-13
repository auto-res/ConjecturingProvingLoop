

theorem interior_closure_interior_closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure (A : Set X)))))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure (interior (closure A)))))))
        = interior (closure (interior (closure (interior (closure A))))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure (interior (closure A)))))
    _ = interior (closure (interior (closure A))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure A)))
    _ = interior (closure A) := by
          simpa using
            (interior_closure_interior_closure_eq (A := A))