

theorem closure_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (closure (interior (A : Set X))) = closure (interior (A : Set X)) := by
  simpa [closure_closure]