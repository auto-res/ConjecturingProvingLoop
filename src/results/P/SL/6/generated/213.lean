

theorem P3_iff_P1_and_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P3 (A : Set X) ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Existing equivalences on open sets.
  have h3_2 : Topology.P3 (A : Set X) ↔ Topology.P2 A :=
    Topology.P3_iff_P2_of_isOpen (A := A) hA
  have h1_2 : Topology.P1 (A : Set X) ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  constructor
  · intro hP3
    -- Derive `P2` from `P3`, then `P1` from `P2`.
    have hP2 : Topology.P2 (A : Set X) := (h3_2).1 hP3
    have hP1 : Topology.P1 (A : Set X) := (h1_2).2 hP2
    exact And.intro hP1 hP2
  · rintro ⟨_hP1, hP2⟩
    -- Convert `P2` back to `P3`.
    exact (h3_2).2 hP2