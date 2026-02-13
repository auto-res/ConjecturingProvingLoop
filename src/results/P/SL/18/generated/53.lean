

theorem P2_implies_P1_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  have hOpen : IsOpen A :=
    (Topology.P2_closed_iff_open hA_closed).1 hP2
  exact Topology.P1_of_open hOpen