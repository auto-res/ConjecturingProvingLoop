

theorem P2_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 A :=
      Topology.P2_implies_P3 (X := X) (A := A) hP2
    exact
      (Topology.P3_closed_iff_isOpen (X := X) (A := A) hA_closed).mp hP3
  · intro hA_open
    exact Topology.isOpen_implies_P2 (X := X) (A := A) hA_open