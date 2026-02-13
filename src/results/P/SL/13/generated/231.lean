

theorem Topology.P3_iff_P2_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X:=X) A) :
    Topology.P3 (X:=X) A ↔ Topology.P2 (X:=X) A := by
  constructor
  · intro hP3
    -- Combine the given `P1` with the assumed `P3` to obtain `P2`.
    have hPair : Topology.P1 (X:=X) A ∧ Topology.P3 (X:=X) A := ⟨hP1, hP3⟩
    exact
      (Topology.P2_iff_P1_and_P3 (X:=X) (A:=A)).2 hPair
  · intro hP2
    -- Extract `P3` from `P2`.
    have hPair : Topology.P1 (X:=X) A ∧ Topology.P3 (X:=X) A :=
      (Topology.P2_iff_P1_and_P3 (X:=X) (A:=A)).1 hP2
    exact hPair.2