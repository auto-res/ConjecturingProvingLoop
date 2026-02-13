

theorem Topology.P1_iff_P2_and_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ↔
      (Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A) := by
  constructor
  · intro hP1
    -- Derive `P2` from `P1` using the equivalence for open sets.
    have hP2 : Topology.P2 (X := X) A :=
      (Topology.P1_iff_P2_of_isOpen (X := X) (A := A) hA).1 hP1
    -- Derive `P3` from `P1` using the corresponding equivalence.
    have hP3 : Topology.P3 (X := X) A :=
      (Topology.P1_iff_P3_of_isOpen (X := X) (A := A) hA).1 hP1
    exact And.intro hP2 hP3
  · intro h
    -- From `P2` we can always deduce `P1`.
    exact Topology.P2_implies_P1 (X := X) (A := A) h.1