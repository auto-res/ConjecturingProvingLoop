

theorem Topology.P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  have hP2 : Topology.P2 (X:=X) A ↔ IsOpen (A : Set X) :=
    Topology.P2_iff_isOpen_of_isClosed (X:=X) (A:=A) hA_closed
  have hP3 : Topology.P3 (X:=X) A ↔ IsOpen (A : Set X) :=
    Topology.P3_iff_isOpen_of_isClosed (X:=X) (A:=A) hA_closed
  exact hP2.trans hP3.symm