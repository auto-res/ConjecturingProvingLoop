

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  simpa using (Topology.P3_of_isOpen (A := interior A) isOpen_interior)