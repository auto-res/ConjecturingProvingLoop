

theorem Topology.interiorClosureInterior_idempotent {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (interior A)))) = interior (closure (interior A)) := by
  have h := Topology.closureInteriorClosureInterior_eq_closureInterior (A := A)
  simpa using congrArg interior h