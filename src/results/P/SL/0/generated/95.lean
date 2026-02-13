

theorem P3_implies_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 A → Topology.P2 A := by
  intro hP3
  exact
    (Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hA).mpr hP3