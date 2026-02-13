

theorem Topology.P1_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (closure (interior (closure A))) := by
  dsimp [Topology.P1]
  intro x hx
  -- Use the idempotence lemma to rewrite the target set.
  have h_eq :
      closure (interior (closure (interior (closure A)))) =
        closure (interior (closure A)) := by
    simpa using
      (Topology.closure_interior_closure_interior_eq
        (X := X) (A := closure A))
  -- The goal follows by rewriting with `h_eq`.
  simpa [h_eq] using hx