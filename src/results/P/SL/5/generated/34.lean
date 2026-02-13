

theorem closure_interior_idempotent_four {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
      closure (interior A) := by
  -- The three-step idempotency.
  have h3 :=
    Topology.closure_interior_idempotent_three (X := X) (A := A)
  -- Apply `closure ∘ interior` once more to both sides.
  have h4 :
      closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
    simpa using (congrArg (fun S : Set X => closure (interior S)) h3)
  -- The basic idempotency.
  have h1 :=
    Topology.closure_interior_idempotent (X := X) (A := A)
  -- Assemble the equalities.
  calc
    closure (interior (closure (interior (closure (interior (closure (interior A))))))) =
        closure (interior (closure (interior A))) := by
          simpa using h4
    _ = closure (interior A) := by
          simpa using h1