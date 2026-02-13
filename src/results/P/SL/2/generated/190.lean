

theorem Topology.closure_interior_closure_interior_closure_interior_closure_interior_eq_closure_interior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- First collapse the two outermost `closure ∘ interior` cycles.
  have h₁ :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior (closure (interior A))))) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq_closure_interior
        (A := closure (interior (closure (interior (closure (interior A)))))))
  -- Next collapse the remaining three–cycle, using the already-established idempotency.
  have h₂ :
      closure (interior (closure (interior (closure (interior A))))) =
        closure (interior A) :=
    Topology.closure_interior_closure_interior_closure_interior_eq_closure_interior (A := A)
  -- Put the two reductions together.
  simpa [h₁] using h₂