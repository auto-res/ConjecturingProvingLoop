

theorem P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  dsimp [Topology.P3, Topology.P1] at hP3 ⊢
  exact closure_mono hP3