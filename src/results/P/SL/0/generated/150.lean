

theorem P2_implies_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) :
    Topology.P2 A → Topology.P3 A := by
  intro hP2
  have hEquiv := Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hClosed
  exact (hEquiv).mp hP2