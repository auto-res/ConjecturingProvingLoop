

theorem closed_P2_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    exact Topology.closed_P2_isOpen (X := X) (A := A) hA_closed hP2
  · intro hA_open
    exact Topology.isOpen_imp_P2 (X := X) (A := A) hA_open