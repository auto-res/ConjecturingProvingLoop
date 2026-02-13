

theorem Topology.P3_union_open_left {X : Type*} [TopologicalSpace X] {U A : Set X}
    (hU : IsOpen U) :
    Topology.P3 A → Topology.P3 (U ∪ A) := by
  intro hP3A
  have hP3U : Topology.P3 U :=
    Topology.isOpen_implies_P3 (X := X) (A := U) hU
  simpa using
    Topology.P3_union (X := X) (A := U) (B := A) hP3U hP3A