

theorem P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  intro x hxCl
  have hsubset : (closure A : Set X) ⊆ closure (interior (closure A)) :=
    closure_mono hP3
  exact hsubset hxCl