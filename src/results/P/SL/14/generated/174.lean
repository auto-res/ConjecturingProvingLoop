

theorem Topology.interiorClosure_iterate_idempotent₂
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior (closure (interior A)))))) =
      interior (closure (interior A)) := by
  -- First reduction using idempotence on `interior (closure (interior A))`.
  have h1 :
      interior (closure (interior (closure (interior (closure (interior A)))))) =
        interior (closure (interior (closure (interior A)))) := by
    simpa using
      (Topology.interiorClosure_idempotent
        (X := X) (A := interior (closure (interior A))))
  -- Second reduction using idempotence on `interior A`.
  have h2 :
      interior (closure (interior (closure (interior A)))) =
        interior (closure (interior A)) := by
    simpa using
      (Topology.interiorClosure_idempotent
        (X := X) (A := interior A))
  -- Combine the two equalities.
  simpa using (h1.trans h2)