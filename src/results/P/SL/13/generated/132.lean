

theorem Topology.closed_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X:=X) A) :
    Topology.P2 (X:=X) A := by
  have h_equiv := Topology.P2_iff_P3_of_isClosed (X:=X) (A:=A) hA_closed
  exact h_equiv.mpr hP3