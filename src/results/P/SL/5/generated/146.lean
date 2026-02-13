

theorem interior_interior_closure_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (interior (closure (A : Set X))) = interior (closure A) := by
  simpa using interior_interior (closure (A : Set X))