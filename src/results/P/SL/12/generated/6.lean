

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (X := X) (interior A) := by
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa using Topology.isOpen_P2 (X := X) (A := interior A) h_open