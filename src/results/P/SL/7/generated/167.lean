

theorem Topology.interiorClosure_iter5_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior
      (closure (interior (closure A))))))))) =
      interior (closure A) := by
  -- Apply the 4-fold idempotence lemma to `interior (closure A)`.
  have h :=
    Topology.interiorClosure_iter4_idempotent (A := interior (closure A))
  -- Simplify the right‐hand side using the basic idempotence lemma.
  simpa [Topology.interiorClosure_idempotent (A := A)] using h