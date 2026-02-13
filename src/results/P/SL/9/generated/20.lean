

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (A := interior A) := by
  exact Topology.P3_of_isOpen (A := interior A) isOpen_interior