

theorem Topology.interiorClosureInterior_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior A)))) =
      interior (closure (interior A)) := by
  simpa using
    (Topology.interiorClosure_idempotent (X := X) (A := interior A))