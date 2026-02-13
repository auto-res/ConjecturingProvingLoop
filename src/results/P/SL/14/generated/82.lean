

theorem Topology.interiorClosure_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) ∧
      Topology.P2 (interior (closure A)) ∧
      Topology.P3 (interior (closure A)) := by
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  simpa using
    Topology.isOpen_satisfies_P1_P2_P3
      (X := X) (A := interior (closure A)) hOpen