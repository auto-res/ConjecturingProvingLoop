

theorem Topology.P3_iff_P1_and_P2_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    Topology.P3 A ↔ (Topology.P1 A ∧ Topology.P2 A) := by
  -- Existing equivalences for open sets.
  have h1 : Topology.P1 A ↔ Topology.P3 A :=
    Topology.P1_iff_P3_of_isOpen (A := A) hA
  have h2 : Topology.P1 A ↔ Topology.P2 A :=
    Topology.P1_iff_P2_of_isOpen (A := A) hA
  -- Prove each direction of the desired equivalence.
  constructor
  · intro hP3
    -- Obtain `P1` from `P3` using `h1`.
    have hP1 : Topology.P1 A := (h1.symm).mp hP3
    -- Obtain `P2` from `P1` using `h2`.
    have hP2 : Topology.P2 A := h2.mp hP1
    exact And.intro hP1 hP2
  · rintro ⟨hP1, _⟩
    -- Derive `P3` from `P1` using `h1`.
    exact h1.mp hP1