

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  exact Topology.isOpen_implies_P2 (X := X) (A := interior A) hOpen