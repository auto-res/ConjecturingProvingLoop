

theorem Topology.closureInterior_iterate_idempotent₂
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First, apply the three–step idempotence lemma to `closure (interior A)`.
  have h₁ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using
      (Topology.closureInterior_iterate_idempotent
        (X := X) (A := closure (interior A)))
  -- Next, reduce the right‐hand side using the basic idempotence lemma.
  have h₂ :
      closure (interior (closure (interior A))) =
        closure (interior A) := by
    simpa using
      (Topology.closureInterior_idempotent (X := X) (A := A))
  -- Combine the two equalities to obtain the desired result.
  simpa using h₁.trans h₂