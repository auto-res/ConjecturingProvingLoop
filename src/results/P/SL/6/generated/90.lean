

theorem interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
      interior (closure A) := by
  calc
    interior (closure (interior (closure (interior (closure (A : Set X)))))) =
        interior (closure (interior (closure (A : Set X)))) := by
          simpa using
            (interior_closure_interior_closure_eq
              (A := interior (closure (A : Set X))))
    _ = interior (closure (A : Set X)) := by
          simpa using
            (interior_closure_interior_closure_eq (A := A))