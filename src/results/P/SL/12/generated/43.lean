

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ IsOpen (A : Set X) := by
  constructor
  · intro hP2
    have hP3 : Topology.P3 (X := X) A :=
      Topology.P2_implies_P3 (X := X) (A := A) hP2
    exact
      (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) h_closed).1 hP3
  · intro h_open
    exact Topology.isOpen_P2 (X := X) (A := A) h_open