

theorem Topology.P1_iff_P2_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 (X:=X) A) :
    Topology.P1 (X:=X) A ↔ Topology.P2 (X:=X) A := by
  have h := (Topology.P2_iff_P1_of_P3 (X:=X) (A:=A) hP3)
  simpa using h.symm