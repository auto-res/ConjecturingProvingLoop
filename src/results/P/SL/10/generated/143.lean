

theorem Topology.P2_union_open_left {X : Type*} [TopologicalSpace X] {U A : Set X}
    (hU : IsOpen U) :
    Topology.P2 A → Topology.P2 (U ∪ A) := by
  intro hP2A
  have hP2U : Topology.P2 U :=
    Topology.isOpen_implies_P2 (X := X) (A := U) hU
  simpa using
    Topology.P2_union (X := X) (A := U) (B := A) hP2U hP2A