

theorem Topology.P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    exact Topology.isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
  · intro hOpen
    exact Topology.P3_of_isOpen (A := A) hOpen