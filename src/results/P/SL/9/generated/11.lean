

theorem Topology.P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 (A := A)) :
    Topology.P1 (A := A) := by
  have hA_open : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA_closed).1 hP3
  exact Topology.P1_of_isOpen (A := A) hA_open