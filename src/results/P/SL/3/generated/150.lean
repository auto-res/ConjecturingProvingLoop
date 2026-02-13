

theorem interior_closure_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (interior (A : Set X)))) =
      interior (closure (interior (A : Set X))) := by
  simpa using
    (interior_closure_closure (A := interior (A : Set X)))