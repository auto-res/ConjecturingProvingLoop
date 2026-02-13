

theorem Topology.P3_implies_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) : Topology.P3 A → Topology.P2 A := by
  intro hP3
  have hOpen : IsOpen A :=
    Topology.isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  exact Topology.P2_of_isOpen (A := A) hOpen