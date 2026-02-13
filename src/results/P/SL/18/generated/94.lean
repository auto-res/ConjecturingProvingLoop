

theorem P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure (A : Set X)) := by
  intro hP3
  -- Unfold definitions of `P3` and `P1`.
  dsimp [Topology.P3] at hP3
  dsimp [Topology.P1]
  intro x hxCl
  -- Use monotonicity of `closure` with the inclusion given by `hP3`.
  have hIncl : closure (A : Set X) ⊆ closure (interior (closure A)) := by
    apply closure_mono
    exact hP3
  exact hIncl hxCl