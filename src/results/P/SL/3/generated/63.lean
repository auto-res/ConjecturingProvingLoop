

theorem interior_closure_interior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (A : Set X))))) =
      interior (closure (interior (A : Set X))) := by
  have h := closure_interior_closure_interior (A := A)
  simpa using congrArg interior h