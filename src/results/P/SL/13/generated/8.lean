

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 (X:=X) A ↔ Topology.P2 (X:=X) A := by
  refine ⟨fun _ => isOpen_implies_P2 (X:=X) (A:=A) hA, ?_⟩
  intro hP2
  exact Topology.P2_implies_P1 (X:=X) (A:=A) hP2