

theorem Topology.interior_closure_interior_closure_interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  -- First, compress the innermost five-step pattern.
  have h₁ :
      interior (closure (interior (closure (interior A)))) =
        interior (closure (interior A)) :=
    interior_closure_interior_idempotent (A := A)
  -- Substitute the reduction and apply the two-step idempotency lemma.
  simpa [h₁] using
    (interior_closure_idempotent (A := interior A))