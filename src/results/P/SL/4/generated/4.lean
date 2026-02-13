

theorem P2_imp_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  exact And.intro (Topology.P2_imp_P1 hP2) (Topology.P2_imp_P3 hP2)