

theorem interior_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior A) ↔ Topology.P3 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using
    Topology.isOpen_P1_iff_P3 (X := X) (A := interior A) h_open