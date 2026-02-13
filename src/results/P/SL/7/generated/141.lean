

theorem Topology.P2_iff_P3_of_interiorClosureInterior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hEq : interior (closure (interior A)) = interior (closure A)) :
    Topology.P2 A ↔ Topology.P3 A := by
  simpa [Topology.P2, Topology.P3, hEq]