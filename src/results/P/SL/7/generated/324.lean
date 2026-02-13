

theorem Topology.interiorClosureInterior_eq_closureInterior_of_isOpen_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior A))) :
    interior (closure (interior A)) = closure (interior A) := by
  simpa using hOpen.interior_eq