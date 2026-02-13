

theorem P2_iff_P3_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior (A : Set X)) ↔ Topology.P3 (interior (A : Set X)) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P2_iff_P3_of_isOpen
      (X := X) (A := interior (A : Set X)) hOpen)