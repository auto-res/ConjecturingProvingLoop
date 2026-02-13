

theorem P3_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P1 (closure A) := by
  intro hP3
  dsimp [Topology.P1]
  intro x hx_closureA
  -- From `P3`, we have `A ⊆ interior (closure A)`.
  have hA_in : (A : Set X) ⊆ interior (closure A) := by
    dsimp [Topology.P3] at hP3
    exact hP3
  -- Taking closures preserves inclusions.
  have h_subset : closure A ⊆ closure (interior (closure A)) :=
    closure_mono hA_in
  exact h_subset hx_closureA