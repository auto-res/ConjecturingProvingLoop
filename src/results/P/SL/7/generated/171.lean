

theorem Topology.P2_iff_P1_and_P3_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A) := by
  -- Equivalences available for open sets
  have hP1P2 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  have hP1P3 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  -- Establish the two directions of the desired equivalence
  constructor
  · intro hP2
    -- From `P2` obtain `P1`, then `P3`
    have hP1 : Topology.P1 A := hP1P2.mpr hP2
    have hP3 : Topology.P3 A := hP1P3.mp hP1
    exact ⟨hP1, hP3⟩
  · rintro ⟨hP1, _hP3⟩
    -- From `P1` recover `P2`
    exact hP1P2.mp hP1