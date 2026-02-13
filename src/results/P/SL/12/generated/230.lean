

theorem Topology.P1_iff_P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (interior A) ↔ Topology.P2 (X := X) (interior A) := by
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa using
    (Topology.P1_iff_P2_of_isOpen (X := X) (A := interior A) h_open)