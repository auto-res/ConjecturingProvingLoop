

theorem Topology.P2_of_P1_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) (hP1 : Topology.P1 A) : Topology.P2 A := by
  exact ((Topology.P1_iff_P2_of_isOpen (A := A) hA).1) hP1