

theorem closure_interior_closure_interior_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (interior (A : Set X))))) =
      closure (interior A) := by
  simpa [interior_interior] using
    (closure_interior_closure_interior_eq (A := interior (A : Set X)))