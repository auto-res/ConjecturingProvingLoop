

theorem Topology.closed_P2_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP2 : Topology.P2 (X := X) A) :
    IsOpen A := by
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  exact Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3