

theorem Topology.P1_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  have hOpen : IsOpen A :=
    (Topology.clopen_of_isClosed_and_P3 (X := X) (A := A) hA_closed hP3).1
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen