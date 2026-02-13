

theorem Topology.interiorClosure_eq_interiorClosureInterior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (A := A)) :
    interior (closure A) = interior (closure (interior A)) := by
  have hP1 : Topology.P1 (A := A) := Topology.P2_implies_P1 hP2
  simpa using
    (Topology.interiorClosure_eq_interiorClosureInterior_of_P1
      (A := A) hP1)