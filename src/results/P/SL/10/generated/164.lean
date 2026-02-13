

theorem Topology.P3_union_open_right {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hU : IsOpen U) :
    Topology.P3 A → Topology.P3 (A ∪ U) := by
  intro hP3A
  have hP3U : Topology.P3 U :=
    Topology.isOpen_implies_P3 (X := X) (A := U) hU
  simpa using
    Topology.P3_union (X := X) (A := A) (B := U) hP3A hP3U