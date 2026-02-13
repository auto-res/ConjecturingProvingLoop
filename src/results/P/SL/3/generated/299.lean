

theorem Topology.P1_P2_P3_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) ↔ IsOpen (A : Set X) := by
  constructor
  · rintro ⟨_, hP2, _⟩
    exact isOpen_of_isClosed_and_P2 (A := A) hA_closed hP2
  · intro hOpen
    exact Topology.P1_P2_P3_of_isOpen (A := A) hOpen