

theorem interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (A : Set X))))) =
      interior (closure (interior A)) := by
  simpa using
    (interior_closure_interior_closure_eq (A := interior (A : Set X)))