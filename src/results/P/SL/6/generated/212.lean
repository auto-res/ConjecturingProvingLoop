

theorem closure_interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior (closure (A : Set X))))))))) =
      closure (interior (closure A)) := by
  simp [closure_interior_closure_interior_closure_eq,
        closure_closure, interior_interior]