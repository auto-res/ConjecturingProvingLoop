

theorem interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (interior A))) =
      interior (closure (interior A)) := by
  simpa [interior_idempotent]