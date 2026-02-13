

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior (A : Set X)) := by
  have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
  exact isOpen_implies_P2 (X := X) (A := interior A) h_open