

theorem interior_closure_idempotent_iter {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  simpa using interior_closure_idempotent (X := X) (A := interior A)