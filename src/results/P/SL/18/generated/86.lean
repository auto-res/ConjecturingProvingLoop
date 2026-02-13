

theorem P1_and_P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  exact ⟨Topology.P2_implies_P1 hP2, Topology.P2_implies_P3 hP2⟩