

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (A := interior A) := by
  exact Topology.P2_of_isOpen (A := interior A) isOpen_interior