

theorem Topology.interiorClosure_iter2_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  -- First, use idempotence for `closure (interior _ )` with `A := closure A`.
  have h₁ :
      closure (interior (closure (interior (closure (A : Set X))))) =
        closure (interior (closure (A : Set X))) := by
    simpa using
      (Topology.closureInteriorClosureInterior_eq_closureInterior
        (A := closure (A : Set X)))
  -- Apply `interior` to both sides of this equality.
  have h₂ :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) :=
    congrArg interior h₁
  -- Use the basic idempotence lemma to simplify the right‐hand side.
  have h₃ :
      interior (closure (interior (closure A))) =
        interior (closure A) :=
    Topology.interiorClosure_idempotent (A := A)
  -- Combine the results.
  simpa [h₃] using h₂