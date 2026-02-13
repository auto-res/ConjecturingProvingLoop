

theorem closure_closure_interior_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure (interior (A : Set X))) = closure (interior A) := by
  simpa [closure_closure]