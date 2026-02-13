

theorem Topology.P1_and_P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P2 A) ↔ IsOpen A := by
  constructor
  · intro h
    exact
      (Topology.P2_closed_iff_isOpen (A := A) hA).1 h.2
  · intro hOpen
    exact ⟨Topology.IsOpen_P1 (A := A) hOpen, IsOpen_P2 (A := A) hOpen⟩