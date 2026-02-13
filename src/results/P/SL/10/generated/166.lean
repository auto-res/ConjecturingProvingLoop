

theorem Topology.P2_union_open_right {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hU : IsOpen U) :
    Topology.P2 A → Topology.P2 (A ∪ U) := by
  intro hP2A
  have h := Topology.P2_union_open_left (X := X) (U := U) (A := A) hU hP2A
  simpa [Set.union_comm] using h