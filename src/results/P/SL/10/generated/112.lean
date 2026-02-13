

theorem Topology.P2_inter_open_right {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hU : IsOpen U) :
    Topology.P2 A → Topology.P2 (A ∩ U) := by
  intro hP2
  have h := Topology.P2_inter_open_left (X := X) (U := U) (A := A) hU hP2
  simpa [Set.inter_comm] using h