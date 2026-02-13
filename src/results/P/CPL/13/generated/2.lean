

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (interior A) := by
  simpa using (Topology.P2_of_open (A := interior A) isOpen_interior)

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A := by
  exact Topology.P2_implies_P3 (A := A) (Topology.P2_of_open (A := A) hA)