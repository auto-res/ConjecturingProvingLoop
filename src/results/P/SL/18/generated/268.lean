

theorem P1_iff_P2_and_P3_of_open
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (A : Set X)) :
    Topology.P1 A ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  constructor
  · intro _hP1
    exact ⟨Topology.P2_of_open hOpen, Topology.P3_of_open hOpen⟩
  · intro h
    exact Topology.P2_implies_P1 h.1