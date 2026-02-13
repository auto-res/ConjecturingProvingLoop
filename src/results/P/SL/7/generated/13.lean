

theorem Topology.P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  have h := (IsOpen_P1_and_P3 (A := interior A) isOpen_interior).2
  simpa using h