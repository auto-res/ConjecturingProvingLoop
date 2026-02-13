

theorem Topology.P1_and_P3_iff_isOpen_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P3 A) ↔ IsOpen A := by
  constructor
  · intro h
    exact
      (Topology.P3_closed_iff_isOpen (A := A) hA).1 h.2
  · intro hOpen
    exact (Topology.IsOpen_P1_and_P3 (A := A) hOpen)