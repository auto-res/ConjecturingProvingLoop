

theorem P2_implies_P1_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hP2
  have hP3 : Topology.P3 (A : Set X) :=
    Topology.P2_implies_P3 (A := A) hP2
  exact (Topology.P3_implies_P1_of_closed (A := A) hA) hP3