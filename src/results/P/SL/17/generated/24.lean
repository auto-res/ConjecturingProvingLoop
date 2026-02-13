

theorem Topology.P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P2 A ↔ IsOpen A := by
  constructor
  · intro hP2
    exact Topology.isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  · intro hOpen
    exact Topology.P2_of_isOpen (A := A) hOpen