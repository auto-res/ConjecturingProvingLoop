

theorem closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  calc
    closure (interior (closure (interior (closure (interior (closure (interior A)))))))
        = closure (interior (closure (interior (closure (interior A))))) := by
          simpa using
            (closure_interior_closure_interior_closure_eq
                (A := closure (interior (closure (interior A)))))
    _ = closure (interior (closure (interior A))) := by
          simpa using
            (closure_interior_closure_interior_closure_eq
                (A := closure (interior A)))
    _ = closure (interior A) := by
          simpa using
            (closure_interior_closure_interior_closure_eq (A := A))