

theorem Topology.P1_interior_iff_P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔ Topology.P2 (interior A) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  simpa using (Topology.isOpen_P1_iff_P2 (A := interior A) hOpen)