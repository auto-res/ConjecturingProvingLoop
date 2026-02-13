

theorem closure_interior_interior_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (interior (A : Set X))) =
      closure (interior (A : Set X)) := by
  simpa [interior_interior]