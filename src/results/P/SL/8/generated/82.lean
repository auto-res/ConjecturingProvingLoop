

theorem interior_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) ↔ Topology.P3 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    Topology.isOpen_P2_iff_P3 (X := X) (A := interior A) h_open