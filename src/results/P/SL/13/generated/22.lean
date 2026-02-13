

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (X:=X) A ↔ IsOpen (A : Set X) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 (X:=X) A :=
      Topology.P2_implies_P3 (X:=X) (A:=A) hP2
    exact Topology.closed_P3_implies_isOpen (X:=X) (A:=A) hA_closed hP3
  · intro hA_open
    exact isOpen_implies_P2 (X:=X) (A:=A) hA_open