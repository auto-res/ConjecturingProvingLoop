

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  simpa using (IsOpen_P2 (A := interior A) isOpen_interior)