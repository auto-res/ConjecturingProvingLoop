

theorem Topology.P1_closure_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (interior (closure (interior A)))) := by
  -- Two useful equalities coming from idempotence of `closure ∘ interior`.
  have h_eq :
      closure (interior (closure (interior A))) =
        closure (interior A) := by
    simpa using Topology.closure_interior_idempotent (A := A)
  have h_int_eq :
      interior (closure (interior (closure (interior A)))) =
        interior (closure (interior A)) := by
    simpa using Topology.interior_closure_idempotent (A := interior A)
  -- `P1` is already known for `closure (interior A)`.
  have hP1_base : Topology.P1 (closure (interior A)) :=
    Topology.P1_closure_interior (A := A)
  -- Unfold the definition of `P1` and start the proof.
  unfold Topology.P1 at *
  intro x hx
  -- Transport `x` to the simpler set using `h_eq`.
  have hx_base : x ∈ closure (interior A) := by
    simpa [h_eq] using hx
  -- Apply `P1` for `closure (interior A)`.
  have hx_goal_base : x ∈ closure (interior (closure (interior A))) :=
    hP1_base hx_base
  -- Rewrite using `h_int_eq` to match the required target set.
  simpa [h_int_eq] using hx_goal_base