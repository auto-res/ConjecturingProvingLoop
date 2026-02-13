

theorem Topology.P1_inter_open_left {X : Type*} [TopologicalSpace X] {U A : Set X} :
    IsOpen U → Topology.P1 A → Topology.P1 (U ∩ A) := by
  intro hUopen hP1A
  simpa [Set.inter_comm] using
    (Topology.P1_inter_open (A := A) (U := U) hP1A hUopen)