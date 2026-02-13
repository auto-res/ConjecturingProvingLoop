

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  exact Topology.isOpen_implies_P3 (X := X) (A := interior A) h_open