

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  exact Topology.isOpen_implies_P3 (A := interior A) hOpen