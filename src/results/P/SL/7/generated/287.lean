

theorem Topology.P2_inter_open_left {X : Type*} [TopologicalSpace X] {A U : Set X} :
    IsOpen A → Topology.P2 U → Topology.P2 (A ∩ U) := by
  intro hOpenA hP2U
  have h := Topology.P2_inter_open (A := U) (U := A) hP2U hOpenA
  simpa [Set.inter_comm] using h