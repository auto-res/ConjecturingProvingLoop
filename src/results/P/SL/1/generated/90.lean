

theorem Topology.P2_iff_P1_and_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- Established equivalences for open sets.
  have h1 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h2 : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (A := A) hA
  -- Prove each direction of the desired equivalence.
  constructor
  · intro hP2
    have hP1 : Topology.P1 A := h1.mpr hP2
    have hP3 : Topology.P3 A := h2.mp hP2
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _⟩
    exact h1.mp hP1