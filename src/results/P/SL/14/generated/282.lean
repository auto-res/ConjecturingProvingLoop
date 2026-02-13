

theorem Topology.P2_iff_P1_and_P3_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- Existing equivalences for open sets.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  -- Prove each implication separately.
  constructor
  · intro hP2
    have hP1 : Topology.P1 A := (h₁).mpr hP2
    have hP3 : Topology.P3 A := (h₂).1 hP2
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _hP3⟩
    exact (h₁).1 hP1