

theorem P2_of_P1_P3 {X} [TopologicalSpace X] {A : Set X} : P1 A → P3 A → P2 A := by
  intro hP1 hP3
  intro x hxA
  -- `P3` gives `x ∈ interior (closure A)`.
  have hx_int_closureA : x ∈ interior (closure A) := hP3 hxA
  -- From `P1`, we have `A ⊆ closure (interior A)`.
  -- Taking closures yields `closure A ⊆ closure (interior A)`.
  have h_subset : (closure (A : Set X)) ⊆ closure (interior A) := by
    have h' : (A : Set X) ⊆ closure (interior A) := hP1
    simpa [closure_closure] using (closure_mono h')
  -- Monotonicity of `interior` upgrades the inclusion.
  have h_subset_int :
      interior (closure A) ⊆ interior (closure (interior A)) :=
    interior_mono h_subset
  -- Conclude the goal.
  exact h_subset_int hx_int_closureA