

theorem P1_iff_P2_and_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    Topology.P1 (A : Set X) ↔ (Topology.P2 A ∧ Topology.P3 A) := by
  constructor
  · intro hP1
    have hP2 : Topology.P2 (A : Set X) :=
      (Topology.P1_iff_P2_of_isOpen (A := A) hA).1 hP1
    have hP3 : Topology.P3 (A : Set X) :=
      (Topology.P1_iff_P3_of_isOpen (A := A) hA).1 hP1
    exact And.intro hP2 hP3
  · rintro ⟨hP2, _hP3⟩
    exact (Topology.P1_iff_P2_of_isOpen (A := A) hA).2 hP2