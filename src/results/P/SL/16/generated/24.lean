

theorem Topology.closed_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hP3 : Topology.P3 (X := X) A) :
    Topology.P2 (X := X) A := by
  have hOpen : IsOpen A := Topology.closed_P3_isOpen (X := X) (A := A) hClosed hP3
  exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen