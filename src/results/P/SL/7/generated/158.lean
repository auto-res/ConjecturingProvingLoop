

theorem Topology.interiorClosureClosureInterior_eq_interiorClosureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (closure (interior (A : Set X)))) =
      interior (closure (interior A)) := by
  simpa using
    (Topology.interiorClosureClosure_eq_interiorClosure (A := interior A))