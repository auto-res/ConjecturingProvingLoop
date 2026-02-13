

theorem closed_P3_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    exact Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3
  · intro hA_open
    exact Topology.isOpen_imp_P3 (X := X) (A := A) hA_open