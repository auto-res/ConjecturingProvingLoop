

theorem Topology.P3_implies_P1_and_P2_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    Topology.P1 A ∧ Topology.P2 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_isClosed_and_P3 (X := X) (A := A) hA_closed hP3
  have hP2 : Topology.P2 A :=
    Topology.P2_of_isClosed_and_P3 (X := X) (A := A) hA_closed hP3
  exact And.intro hP1 hP2