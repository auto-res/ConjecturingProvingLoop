

theorem Topology.P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A → Topology.P1 A := by
  intro hP3
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  exact Topology.P1_of_isOpen (A := A) hOpen