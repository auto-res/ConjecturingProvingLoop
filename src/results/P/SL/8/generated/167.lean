

theorem closure_interior_closure_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (closure A))) =
      closure (interior (closure A)) := by
  simp [closure_closure, interior_closure_closure_eq]