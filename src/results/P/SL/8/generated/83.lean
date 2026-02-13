

theorem isOpen_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  have hP1 : Topology.P1 A :=
    Topology.isOpen_imp_P1 (X := X) (A := A) hA
  have hP2 : Topology.P2 A :=
    Topology.isOpen_imp_P2 (X := X) (A := A) hA
  have hP3 : Topology.P3 A :=
    Topology.isOpen_imp_P3 (X := X) (A := A) hA
  exact And.intro hP1 (And.intro hP2 hP3)