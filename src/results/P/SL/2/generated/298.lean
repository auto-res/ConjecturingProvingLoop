

theorem Topology.isOpen_P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A)) := by
  intro hOpen
  -- Equivalences available for open sets
  have hP1P2 : Topology.P1 A ↔ Topology.P2 A :=
    (Topology.isOpen_P1_iff_P2 (A := A) hOpen)
  have hP2P3 : Topology.P2 A ↔ Topology.P3 A :=
    (Topology.isOpen_P2_iff_P3 (A := A) hOpen)
  constructor
  · intro hP2
    -- Deduce `P1` from `P2`
    have hP1 : Topology.P1 A := (hP1P2).mpr hP2
    -- Deduce `P3` from `P2`
    have hP3 : Topology.P3 A := (hP2P3).1 hP2
    exact And.intro hP1 hP3
  · rintro ⟨hP1, _hP3⟩
    -- Obtain `P2` from `P1`
    exact (hP1P2).1 hP1