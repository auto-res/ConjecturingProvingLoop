

theorem interior_closure_interior_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (interior (A : Set X)))) =
      interior (closure (interior A)) := by
  simpa [interior_interior]