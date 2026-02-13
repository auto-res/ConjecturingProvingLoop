

theorem Topology.P1_union_open_right {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hU : IsOpen U) :
    Topology.P1 A → Topology.P1 (A ∪ U) := by
  intro hP1A
  have h := Topology.P1_union_open_left (X := X) (U := U) (A := A) hU hP1A
  simpa [Set.union_comm] using h