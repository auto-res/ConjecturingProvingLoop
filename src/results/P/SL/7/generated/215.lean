

theorem Topology.P2_of_P3_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) (hP3 : Topology.P3 A) : Topology.P2 A := by
  exact (Topology.P2_iff_P3_of_isOpen (A := A) hA).mpr hP3