

theorem Topology.interiorClosureInterior_interior_eq {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior (interior A))) = interior (closure (interior A)) := by
  simpa [interior_interior]