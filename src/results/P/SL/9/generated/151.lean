

theorem closure_interior_closure_interior_closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, compress the innermost five-step sequence using the existing lemma
  -- with `A := closure (interior A)`.
  have h₁ :=
    closure_interior_closure_interior_closure_interior_idempotent
      (A := closure (interior A))
  -- Next, compress the remaining three-step sequence.
  have h₂ := closure_interior_closure_idempotent (A := A)
  -- Combine the two equalities.
  calc
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
          simpa using h₁
    _ = closure (interior A) := by
          simpa using h₂