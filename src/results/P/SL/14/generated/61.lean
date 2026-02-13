

theorem Topology.closureInteriorClosure_idempotent
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior (closure A)))) =
      closure (interior (closure A)) := by
  simpa using
    (Topology.closureInterior_idempotent (X := X) (A := closure A))