

theorem interior_closure_interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  -- First apply the idempotence lemma to the inner expression.
  have h₁ :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
    simpa using
      (interior_closure_interior_closure_eq
        (A := interior (closure A)))
  -- A second application collapses one more layer.
  have h₂ :
      interior (closure (interior (closure A))) =
        interior (closure A) :=
    interior_closure_interior_closure_eq (A := A)
  -- Combine the two equalities to obtain the desired result.
  simpa [h₂] using h₁