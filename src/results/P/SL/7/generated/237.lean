

theorem Topology.interiorClosure_iter6_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior
      (closure (interior (closure (interior (closure A))))))))))) =
      interior (closure A) := by
  -- Apply the 5-fold idempotence lemma.
  have h₁ :
      interior (closure (interior (closure (interior (closure (interior
        (closure (interior (closure A))))))))) = interior (closure A) :=
    Topology.interiorClosure_iter5_idempotent (A := A)
  -- Substitute `h₁` and finish with the basic idempotence lemma.
  have :
      interior (closure (interior (closure (interior (closure (interior
        (closure (interior (closure (interior (closure A))))))))))) =
        interior (closure (interior (closure A))) := by
    simpa [h₁]
  simpa [Topology.interiorClosure_idempotent (A := A)] using this