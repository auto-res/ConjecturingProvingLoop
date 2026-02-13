

theorem interior_closure_interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
      interior (closure A) := by
  -- First, simplify the innermost three alternating applications.
  have h1 :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure A) := by
    simpa using
      (interior_closure_interior_closure_interior_closure_eq
        (X := X) (A := A))
  -- Use `h1` to rewrite the larger expression.
  have h2 :
      interior (closure (interior (closure (interior (closure (interior (closure A))))))) =
        interior (closure (interior (closure A))) := by
    simpa [h1]
  -- Finally, collapse the remaining two alternating applications.
  simpa
    [interior_closure_interior_closure_eq (X := X) (A := A)]
    using h2