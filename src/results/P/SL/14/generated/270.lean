

theorem Topology.P1_and_P3_of_isClosed_and_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    Topology.P1 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A :=
    Topology.P1_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  have hP3 : Topology.P3 A :=
    Topology.P3_of_isClosed_and_P2 (X := X) (A := A) hA_closed hP2
  exact And.intro hP1 hP3