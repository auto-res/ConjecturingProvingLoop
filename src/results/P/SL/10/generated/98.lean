

theorem Topology.P3_inter_open_right {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hU : IsOpen U) :
    Topology.P3 A → Topology.P3 (A ∩ U) := by
  intro hP3
  have h := Topology.P3_inter_open_left (X := X) (U := U) (A := A) hU hP3
  simpa [Set.inter_comm] using h