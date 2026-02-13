

theorem P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  exact closure_mono hP3