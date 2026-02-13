

theorem closure_interior_closure_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (closure A))) =
      closure (interior (closure A)) := by
  have hInt : interior (closure (closure A)) = interior (closure A) := by
    simpa [closure_closure] using interior_closure_closure_eq (A := A)
  simpa [hInt]