

theorem Topology.P1_P2_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P1 (X := X) A ∧ Topology.P2 (X := X) A ∧ Topology.P3 (X := X) A := by
  have hP1 : Topology.P1 (X := X) A :=
    Topology.isOpen_P1 (X := X) (A := A) hA
  have hP2 : Topology.P2 (X := X) A :=
    Topology.isOpen_P2 (X := X) (A := A) hA
  have hP3 : Topology.P3 (X := X) A :=
    Topology.isOpen_P3 (X := X) (A := A) hA
  exact And.intro hP1 (And.intro hP2 hP3)