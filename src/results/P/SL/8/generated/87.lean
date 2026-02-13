

theorem interior_closure_interior_closureInterior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  have h :=
    closure_interior_closure_interior_eq (X := X) (A := A)
  simpa [h]