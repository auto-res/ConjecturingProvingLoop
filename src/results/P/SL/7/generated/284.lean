

theorem Topology.P3_of_P2_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) (hP2 : Topology.P2 A) : Topology.P3 A := by
  exact (Topology.P2_iff_P3_of_isOpen (A := A) hOpen).1 hP2