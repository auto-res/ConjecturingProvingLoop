

theorem Topology.P2_of_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P3 A → Topology.P2 A := by
  intro hP1 hP3
  exact (Topology.P2_iff_P1_and_P3 (A := A)).2 ⟨hP1, hP3⟩