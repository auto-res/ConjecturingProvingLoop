

theorem interior_P1_iff_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ↔ Topology.P2 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    Topology.isOpen_P1_iff_P2 (X := X) (A := interior A) h_open