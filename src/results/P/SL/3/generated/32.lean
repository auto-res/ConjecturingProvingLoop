

theorem P3_interior_iff_P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior (A : Set X)) ↔ Topology.P2 (interior (A : Set X)) := by
  have hOpen : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P3_iff_P2_of_isOpen (A := interior (A : Set X)) hOpen)