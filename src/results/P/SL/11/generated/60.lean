

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  simpa using
    ((Topology.P1_iff_P2_of_open (A := A) hA).symm.trans
      (Topology.P1_iff_P3_of_open (A := A) hA))