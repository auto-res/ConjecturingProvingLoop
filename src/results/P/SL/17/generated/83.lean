

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure A))) := by
  unfold Topology.P1
  intro x hx
  -- `closure (interior (closure (interior (closure A))))`
  -- coincides with `closure (interior (closure A))`
  have h_eq :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    simpa using
      (Topology.closure_interior_idempotent (A := closure A))
  -- Use the equality to convert the membership hypothesis
  simpa [h_eq] using hx