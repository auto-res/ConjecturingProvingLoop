

theorem P1_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  simpa using
    (Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA).trans
      (Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA)