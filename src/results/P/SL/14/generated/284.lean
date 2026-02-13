

theorem Topology.P3_iff_P1_and_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Existing equivalence between `P1` and `P3` for open sets.
  have h1 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (X := X) (A := A) hA
  -- Existing equivalence between `P1` and `P2` for open sets.
  have h2 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA
  constructor
  · intro hP3
    -- Derive `P1` from `P3`, then `P2` from `P1`.
    have hP1 : Topology.P1 A := (h1).mpr hP3
    have hP2 : Topology.P2 A := (h2).mp hP1
    exact And.intro hP1 hP2
  · rintro ⟨hP1, _hP2⟩
    -- Obtain `P3` from `P1`.
    exact (h1).mp hP1