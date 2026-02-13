

theorem Topology.P3_iff_P1_and_P2_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P3 (X := X) A ↔
      (Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A) := by
  constructor
  · intro hP3
    -- `P1` follows from `P3` for a closed set.
    have hP1 : Topology.P1 (X := X) A :=
      Topology.P3_implies_P1_of_isClosed (X := X) (A := A) hA hP3
    -- `P2` also follows from `P3` for a closed set.
    have hP2 : Topology.P2 (X := X) A :=
      Topology.P3_implies_P2_of_isClosed (X := X) (A := A) hA hP3
    exact And.intro hP1 hP2
  · rintro ⟨_, hP2⟩
    -- `P2` always implies `P3`.
    exact Topology.P2_implies_P3 (X := X) (A := A) hP2