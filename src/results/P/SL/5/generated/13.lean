

theorem closure_interior_idempotent_iter {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using closure_interior_idempotent (X := X) (A := closure A)