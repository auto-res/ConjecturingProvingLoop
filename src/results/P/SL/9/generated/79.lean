

theorem Topology.closureInteriorInterior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]