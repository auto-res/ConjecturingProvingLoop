

theorem Topology.P1_P2_P3_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen A := by
  constructor
  · intro hTriple
    rcases hTriple with ⟨_, _, hP3⟩
    exact (Topology.P3_closed_iff_isOpen (A := A) hA).1 hP3
  · intro hOpen
    exact (Topology.IsOpen_P1_P2_P3 (A := A) hOpen)