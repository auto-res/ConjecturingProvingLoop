

theorem closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  have h := interior_closure_interior_closure_eq (X := X) (A := A)
  simpa [h]