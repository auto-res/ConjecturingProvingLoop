

theorem Topology.P1_iff_P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X:=X) A) :
    Topology.P1 (X:=X) A ↔ Topology.P3 (X:=X) A := by
  -- From the given `P2`, we immediately obtain both `P1` and `P3`.
  have hP1 : Topology.P1 (X:=X) A :=
    Topology.P2_implies_P1 (X:=X) (A:=A) hP2
  have hP3 : Topology.P3 (X:=X) A :=
    Topology.P2_implies_P3 (X:=X) (A:=A) hP2
  -- These witnesses let us establish the equivalence.
  exact ⟨fun _ => hP3, fun _ => hP1⟩