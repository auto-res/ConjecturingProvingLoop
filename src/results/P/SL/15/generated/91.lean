

theorem closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior A))))) =
      closure (interior A) := by
  have h1 :=
    interior_closure_interior_closure_interior_eq (X := X) (A := A)
  have h2 :=
    closure_interior_closure_eq (X := X) (A := A)
  calc
    closure (interior (closure (interior (closure (interior A))))) =
        closure (interior (closure (interior A))) := by
      simpa [h1]
    _ = closure (interior A) := by
      simpa using h2