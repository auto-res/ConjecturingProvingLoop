

theorem P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hP3
  -- `hP3` gives the inclusion `A ⊆ interior (closure A)`
  dsimp [Topology.P3] at hP3
  -- Unfold the goal `P1 (closure A)`
  dsimp [Topology.P1]
  intro x hx
  -- Taking closures preserves inclusions
  have h_incl :
      closure (A : Set X) ⊆ closure (interior (closure (A : Set X))) :=
    closure_mono hP3
  exact h_incl hx