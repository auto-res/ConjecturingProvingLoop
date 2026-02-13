

theorem Topology.P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    Topology.P1 (X := X) (closure A) := by
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P2_implies_P3 (X := X) (A := A) hA
  exact Topology.P3_implies_P1_closure (X := X) (A := A) hP3