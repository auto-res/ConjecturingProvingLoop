

theorem Topology.P3_iff_P1_and_P2_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen (A : Set X)) :
    Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Existing equivalences under the openness assumption.
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P3 A ↔ Topology.P2 A :=
    Topology.P3_iff_P2_of_isOpen (A := A) hA
  -- Combine the equivalences to obtain the desired statement.
  constructor
  · intro hP3
    have hP2 : Topology.P2 A := (h₂.mp) hP3
    have hP1 : Topology.P1 A := (h₁.mpr) hP2
    exact And.intro hP1 hP2
  · rintro ⟨_, hP2⟩
    exact (h₂.mpr) hP2