

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    Topology.isOpen_implies_P2 (X := X) (A := interior A) h_open