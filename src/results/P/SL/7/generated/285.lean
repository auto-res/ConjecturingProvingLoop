

theorem Topology.interiorClosure_iter7_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior
      (closure (interior (closure (interior (closure A))))))))))) =
      interior (closure A) := by
  -- First, reduce the innermost six-fold nest.
  have h₁ :=
    Topology.interiorClosure_iter6_idempotent (A := A)
  -- Apply one more `interior ∘ closure` pair to both sides of `h₁`.
  have h₂ :
      interior (closure (interior (closure
        (interior (closure (interior (closure (interior
          (closure (interior (closure A))))))))))) =
        interior (closure (interior (closure A))) := by
    simpa using
      congrArg (fun S : Set X =>
        interior (closure (interior (closure S)))) h₁
  -- A final use of the basic idempotence lemma completes the proof.
  have h₃ :
      interior (closure (interior (closure A))) =
        interior (closure A) :=
    Topology.interiorClosure_idempotent (A := A)
  simpa [h₃] using h₂