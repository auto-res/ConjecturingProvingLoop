

theorem Topology.P1_union_open {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hP1A : Topology.P1 (X := X) A) (hOpenU : IsOpen U) :
    Topology.P1 (X := X) (A ∪ U) := by
  have hP1U : Topology.P1 (X := X) U :=
    Topology.isOpen_implies_P1 (X := X) (A := U) hOpenU
  exact
    Topology.P1_union (X := X) (A := A) (B := U) hP1A hP1U