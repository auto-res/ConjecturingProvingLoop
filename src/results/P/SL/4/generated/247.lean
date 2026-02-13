

theorem P3_iff_P1_and_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Existing equivalences for open sets
  have h₁ : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have h₂ : Topology.P2 A ↔ Topology.P3 A :=
    Topology.P2_iff_P3_of_isOpen (A := A) hA
  constructor
  · intro hP3
    -- From `P3` obtain `P2`, then `P1`
    have hP2 : Topology.P2 A := (h₂.symm).mp hP3
    have hP1 : Topology.P1 A := (h₁.mpr) hP2
    exact And.intro hP1 hP2
  · rintro ⟨hP1, hP2⟩
    -- From `P2` obtain `P3`
    exact (h₂.mp) hP2