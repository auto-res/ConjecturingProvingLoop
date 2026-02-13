

theorem Topology.P2_and_P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    (Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen A := by
  have hP2 := Topology.P2_closed_iff_isOpen (A := A) hA
  have hP3 := Topology.P3_closed_iff_isOpen (A := A) hA
  constructor
  · intro h
    exact (hP2).1 h.1
  · intro hOpen
    exact ⟨(hP2).2 hOpen, (hP3).2 hOpen⟩