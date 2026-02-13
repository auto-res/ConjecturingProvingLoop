

theorem P1_P2_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (A : Set X)) ∧
      Topology.P2 (interior (A : Set X)) ∧
        Topology.P3 (interior (A : Set X)) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P1_P2_P3_of_isOpen (A := interior (A : Set X)) hOpen)