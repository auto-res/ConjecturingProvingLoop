

theorem P1_and_P2_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) :
    Topology.P3 A → (Topology.P1 A ∧ Topology.P2 A) := by
  intro hP3
  have hP1 : Topology.P1 A :=
    Topology.P3_implies_P1_of_closed (A := A) hClosed hP3
  have hP2 : Topology.P2 A :=
    Topology.P3_implies_P2_of_closed (A := A) hClosed hP3
  exact And.intro hP1 hP2