

theorem Topology.P3_interior_iff_P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P3 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using
    (Topology.isOpen_P2_iff_P3 (A := interior A) hOpen).symm