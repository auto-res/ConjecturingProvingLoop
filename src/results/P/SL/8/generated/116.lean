

theorem interior_closure_interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  have h :=
    interior_closure_interior_closure_interior_closure_interior_closure_eq
      (X := X) (A := closure A)
  simpa [closure_closure] using h