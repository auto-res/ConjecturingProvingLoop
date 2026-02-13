

theorem Topology.closure_interior_closure_interior_closure_interior_closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, simplify the innermost pattern using the existing 3-level idempotence lemma
  -- with `A := closure (interior A)`.
  have h₁ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closure_interior_closure_interior_closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := closure (interior A)))
  -- Next, collapse the remaining expression once more using the 2-level lemma.
  have h₂ :
      closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (X := X) (A := A))
  -- Combine the two equalities to obtain the desired result.
  simpa [h₂] using h₁