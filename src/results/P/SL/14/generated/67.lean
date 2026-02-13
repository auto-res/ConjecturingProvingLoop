

theorem Topology.interiorClosure_iterate_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure A))))) =
      interior (closure A) := by
  -- First reduction using idempotence on `interior (closure A)`.
  have hStep1 :
      interior (closure (interior (closure (interior (closure A))))) =
        interior (closure (interior (closure A))) := by
    simpa using
      (Topology.interiorClosure_idempotent (X := X) (A := interior (closure A)))
  -- Second reduction using idempotence on `A`.
  have hStep2 :
      interior (closure (interior (closure A))) = interior (closure A) := by
    simpa using
      (Topology.interiorClosure_idempotent (X := X) (A := A))
  -- Combine the two equalities.
  simpa using (hStep1.trans hStep2)