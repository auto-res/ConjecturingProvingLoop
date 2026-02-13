

theorem Topology.interior_closure_interior_closure_interior_closure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  have h₁ :=
    (interior_closure_idempotent (A := interior (closure A)))
  have h₂ :=
    (interior_closure_idempotent (A := A))
  simpa using (Eq.trans h₁ h₂)