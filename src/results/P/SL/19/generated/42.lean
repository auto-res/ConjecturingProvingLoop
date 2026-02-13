

theorem Topology.P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 (A := A) → Topology.P1 (A := A) := by
  intro hP3
  have hP2 : Topology.P2 (A := A) :=
    (Topology.P3_implies_P2_of_isClosed (A := A) hA) hP3
  exact Topology.P2_implies_P1 (A := A) hP2