

theorem P2_iff_P1_and_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  constructor
  · intro hP2
    exact And.intro
      (Topology.P2_implies_P1 (A := A) hP2)
      (Topology.P2_implies_P3 (A := A) hP2)
  · rintro ⟨hP1, _hP3⟩
    exact ((Topology.P1_iff_P2_of_isOpen (A := A) hA).1) hP1