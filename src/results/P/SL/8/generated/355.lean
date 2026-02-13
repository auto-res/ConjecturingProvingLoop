

theorem interior_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (interior (closure A)) = interior (closure A) := by
  simpa [interior_interior]