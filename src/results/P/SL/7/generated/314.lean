

theorem Topology.P3_inter_open_left {X : Type*} [TopologicalSpace X] {U A : Set X} :
    IsOpen U → Topology.P3 A → Topology.P3 (U ∩ A) := by
  intro hOpenU hP3A
  have h := Topology.P3_inter_open (A := A) (U := U) hP3A hOpenU
  simpa [Set.inter_comm] using h