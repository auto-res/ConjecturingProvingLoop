

theorem P2_iff_P1_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- Existing equivalences for open sets.
  have h₁ := Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  have h₂ := Topology.P2_iff_P3_of_isOpen (X := X) (A := A) hA
  -- Forward implication: `P2` gives both `P1` and `P3`.
  constructor
  · intro hP2
    have hP1 : Topology.P1 A := (h₁).mpr hP2
    have hP3 : Topology.P3 A := (h₂).mp hP2
    exact And.intro hP1 hP3
  -- Reverse implication: from `P1` (and hence `P2`) obtain `P2`.
  · rintro ⟨hP1, _⟩
    exact (h₁).mp hP1