

theorem P3_implies_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    Topology.P2 (X := X) A := by
  exact
    (Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hClosed).2 hP3