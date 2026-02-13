

theorem interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure (interior (A : Set X))))))))) =
      interior (closure (interior A)) := by
  calc
    interior (closure (interior (closure (interior (closure (interior (closure (interior (A : Set X))))))))) =
        interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure (interior (closure (interior (A : Set X)))))))
    _ = interior (closure (interior (closure (interior (A : Set X))))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure (interior (A : Set X)))))
    _ = interior (closure (interior (A : Set X))) := by
          simpa using
            (interior_closure_interior_closure_eq (A := A))