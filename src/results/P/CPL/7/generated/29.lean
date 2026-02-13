

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (interior A) := by
  simpa using (P1_of_P2 (A := interior A) P2_interior)