

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) := by
  simpa using (Topology.isOpen_implies_P1 (A := interior A) isOpen_interior)