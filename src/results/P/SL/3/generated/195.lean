

theorem interior_closure_interior_triple_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior (A : Set X))))))) =
      interior (closure (interior (A : Set X))) := by
  -- Apply the double idempotent lemma to `closure (interior A)`.
  have h₁ :=
    interior_closure_interior_double_idempotent
      (A := closure (interior (A : Set X)))
  -- Simplify the right‐hand side of `h₁` using the basic idempotent lemma.
  have h₂ :=
    interior_closure_interior_idempotent (A := A)
  simpa [h₂] using h₁