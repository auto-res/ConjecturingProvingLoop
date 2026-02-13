

theorem closure_interior_closure_interior_closure_interior_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, collapse the two outermost layers.
  have h₁ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior (closure (interior A))))) := by
    simpa using
      (closure_interior_closure_interior_eq
        (X := X) (A := closure (interior (closure (interior A)))))
  -- Next, collapse the remaining three layers.
  have h₂ :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior A) := by
    simpa using
      (closure_interior_closure_interior_closure_interior_eq
        (X := X) (A := A))
  -- Combine the two equalities.
  simpa using (h₁.trans h₂)