

theorem closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure A)))))) =
      closure (interior (closure A)) := by
  -- First, collapse the two outermost layers using an existing lemma.
  have h :
      closure (interior (closure (interior (closure (interior (closure A)))))) =
        closure (interior (closure (closure A))) := by
    simpa using
      (closure_interior_closure_interior_closure_eq (X := X) (A := closure A))
  -- Finally, simplify the remaining `closure` and `interior` of a closure.
  simpa [closure_closure, interior_closure_closure_eq] using h