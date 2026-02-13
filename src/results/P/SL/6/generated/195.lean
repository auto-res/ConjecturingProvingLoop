

theorem P1_implies_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → (A ⊆ closure (interior (closure A))) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  intro x hxA
  -- From `P1`, we have `x ∈ closure (interior A)`.
  have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
  -- Monotonicity of `interior` lifts `A ⊆ closure A`.
  have hIncl :
      closure (interior (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) := by
    apply closure_mono
    apply interior_mono
    exact (subset_closure : (A : Set X) ⊆ closure A)
  exact hIncl hx_cl