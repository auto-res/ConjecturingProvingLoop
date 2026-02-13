

theorem closure_interior_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior (closure (A : Set X)))) =
      closure (interior (closure A)) := by
  simpa [interior_interior]