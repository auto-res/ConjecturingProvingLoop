

theorem Topology.P2_iff_P1_and_P3_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact ⟨Topology.P2_implies_P1 (A := A) hP2,
      Topology.P2_implies_P3 (A := A) hP2⟩
  · rintro ⟨_, hP3⟩
    have hOpen : IsOpen (A : Set X) :=
      isOpen_of_isClosed_and_P3 (A := A) hA_closed hP3
    exact Topology.P2_of_isOpen (A := A) hOpen