

theorem P2_iff_P3_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P2 (interior A) ↔ Topology.P3 (interior A) := by
  simpa using
    (Topology.P2_iff_P3_of_open (A := interior A) isOpen_interior)