

theorem interior_closure_closure_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (A : Set X))) = interior (closure A) := by
  simpa [closure_closure]