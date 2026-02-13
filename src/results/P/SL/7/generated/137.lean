

theorem Topology.P2_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) : Topology.P2 A := by
  exact ((Topology.P2_iff_P3_of_isClosed (A := A) hA).2) hP3