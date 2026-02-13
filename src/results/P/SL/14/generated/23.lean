

theorem Topology.P2_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  have hP3_iff := Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA_closed
  constructor
  · intro hP2
    have hP3 : Topology.P3 A :=
      Topology.P2_implies_P3 (X := X) (A := A) hP2
    exact (hP3_iff).1 hP3
  · intro hOpen
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hOpen