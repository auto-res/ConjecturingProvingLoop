

theorem Topology.P1_inter_open_right {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hU : IsOpen U) :
    Topology.P1 A → Topology.P1 (A ∩ U) := by
  intro hP1
  have h := Topology.P1_inter_open_left (X := X) (U := U) (A := A) hU hP1
  simpa [Set.inter_comm] using h