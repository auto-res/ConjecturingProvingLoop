

theorem P2_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (A : Set X)) :
    Topology.P2 A := by
  have hEquiv := Topology.P3_iff_P2_of_isClosed (A := A) hA_closed
  exact hEquiv.mp hP3