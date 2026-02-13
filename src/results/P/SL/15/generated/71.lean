

theorem P3_closed_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A → Topology.P1 A := by
  intro hP3
  have hOpen : IsOpen A :=
    (Topology.P3_closed_iff_isOpen (X := X) (A := A) hA_closed).1 hP3
  exact Topology.isOpen_implies_P1 (X := X) (A := A) hOpen