

theorem interior_closure_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (closure (interior A))) = interior (closure (interior A)) := by
  simpa [closure_closure]