

theorem P1_iff_P2_and_P3_of_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) ↔
      (Topology.P2 (interior A) ∧ Topology.P3 (interior A)) := by
  simpa using
    (Topology.P1_iff_P2_and_P3_of_open (A := interior A) isOpen_interior)