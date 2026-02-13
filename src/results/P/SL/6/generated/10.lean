

theorem P3_iff_P2_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.P3_iff_P2_of_isOpen (A := interior A) hOpen)