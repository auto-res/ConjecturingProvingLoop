

theorem closure_has_P1_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hA
  dsimp [Topology.P3] at hA
  dsimp [Topology.P1]
  exact closure_mono hA