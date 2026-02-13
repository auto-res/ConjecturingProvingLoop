

theorem Topology.P3_iff_P1_and_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Equivalences already established for open sets
  have hP1P3 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  have hP1P2 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  -- Prove each direction of the desired equivalence
  constructor
  · intro hP3
    -- From `P3` obtain `P1`
    have hP1 : Topology.P1 A := (hP1P3).mpr hP3
    -- From `P1` obtain `P2`
    have hP2 : Topology.P2 A := (hP1P2).mp hP1
    exact ⟨hP1, hP2⟩
  · rintro ⟨hP1, _hP2⟩
    -- From `P1` recover `P3`
    exact (hP1P3).mp hP1