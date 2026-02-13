

theorem closure_interior_closure_interior_double_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (A : Set X)))))) =
      closure (interior (A : Set X)) := by
  calc
    closure (interior (closure (interior (closure (interior (A : Set X)))))) =
        closure (interior (closure (interior (A : Set X)))) := by
          simpa using
            closure_interior_closure_interior
              (A := closure (interior (A : Set X)))
    _ = closure (interior (A : Set X)) := by
          simpa using
            closure_interior_closure_interior (A := A)