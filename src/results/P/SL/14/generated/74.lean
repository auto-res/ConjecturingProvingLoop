

theorem Topology.interiorClosure_eq_interiorClosureInterior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  have hP1 : Topology.P1 A :=
    Topology.P2_implies_P1 (X := X) (A := A) hP2
  exact
    Topology.interiorClosure_eq_interiorClosureInterior_of_P1
      (X := X) (A := A) hP1