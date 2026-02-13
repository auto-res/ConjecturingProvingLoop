

theorem closure_interior_closure_interior_closure_interior_eq {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior (closure (interior A))) := by
  have h :=
    interior_closure_interior_closure_interior_eq
      (X := X) (A := A)
  simpa [h]