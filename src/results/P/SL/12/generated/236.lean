

theorem Topology.P1_iff_P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (interior A) ↔ Topology.P3 (X := X) (interior A) := by
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P1_iff_P3_of_isOpen (X := X) (A := interior A) h_open)