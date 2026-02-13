

theorem Topology.isOpen_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) : IsOpen A := by
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact ((Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed).1) hP3