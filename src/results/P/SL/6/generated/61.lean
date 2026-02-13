

theorem closure_interior_closure_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure (A : Set X))))
      = closure (interior (closure A)) := by
  simpa [closure_closure]