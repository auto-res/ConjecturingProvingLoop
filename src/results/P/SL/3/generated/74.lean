

theorem closure_interior_closure_interior_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure (A : Set X))) := by
  simpa using
    (closure_interior_closure_interior (A := closure (A : Set X)))