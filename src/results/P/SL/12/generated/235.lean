

theorem Topology.P2_iff_P1_and_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A) := by
  constructor
  · intro hP2
    -- `P1` follows from `P2` for a closed set.
    have hP1 : Topology.P1 (X := X) A :=
      Topology.P2_implies_P1_of_isClosed (X := X) (A := A) hA hP2
    -- `P3` is equivalent to `P2` for closed sets.
    have hP3 : Topology.P3 (X := X) A := by
      have h_equiv :=
        Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hA
      exact h_equiv.1 hP2
    exact And.intro hP1 hP3
  · rintro ⟨_, hP3⟩
    -- For closed sets, `P3` implies `P2`.
    exact
      Topology.P3_implies_P2_of_isClosed (X := X) (A := A) hA hP3