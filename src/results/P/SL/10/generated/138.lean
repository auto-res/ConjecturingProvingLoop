

theorem Topology.P1_union_open_left {X : Type*} [TopologicalSpace X] {U A : Set X}
    (hU : IsOpen U) :
    Topology.P1 A → Topology.P1 (U ∪ A) := by
  intro hP1A
  have hP1U : Topology.P1 U :=
    Topology.isOpen_implies_P1 (X := X) (A := U) hU
  exact Topology.P1_union (X := X) (A := U) (B := A) hP1U hP1A