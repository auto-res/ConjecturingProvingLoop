

theorem Topology.P2_iff_P1_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- Reuse the existing equivalences between the properties under the openness assumption
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P3 A ↔ Topology.P2 A :=
    Topology.P3_iff_P2_of_isOpen (A := A) hA
  constructor
  · intro hP2
    -- From `P2` we obtain `P1` and `P3` via the equivalences
    have hP1 : Topology.P1 A := (h₁.mpr) hP2
    have hP3 : Topology.P3 A := (h₂.mpr) hP2
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _⟩
    -- From `P1` we recover `P2`; `P3` is not needed for this direction
    exact h₁.mp hP1