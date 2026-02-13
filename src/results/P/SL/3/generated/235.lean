

theorem P1_and_P3_of_closure_eq_interior_fixed {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) = interior (A : Set X) →
      (Topology.P1 A ∧ Topology.P3 A) := by
  intro hEq
  -- First, prove P1.
  have hP1 : Topology.P1 (A : Set X) := by
    dsimp [Topology.P1]
    intro x hxA
    -- From `x ∈ A`, we get `x ∈ closure A`.
    have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    -- Using the hypothesis, `closure A = interior A`, hence `x ∈ interior A`.
    have hx_int : (x : X) ∈ interior (A : Set X) := by
      simpa [hEq] using hx_closure
    -- Finally, `interior A ⊆ closure (interior A)` by `subset_closure`.
    exact subset_closure hx_int
  -- Next, prove P3.
  have hP3 : Topology.P3 (A : Set X) := by
    dsimp [Topology.P3]
    intro x hxA
    -- As above, `x ∈ closure A`.
    have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
    -- Convert this to membership in `interior A` via the hypothesis.
    have hx_int : (x : X) ∈ interior (A : Set X) := by
      simpa [hEq] using hx_closure
    -- Monotonicity of `interior` yields `interior A ⊆ interior (closure A)`.
    have h_sub :
        interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
    exact h_sub hx_int
  exact And.intro hP1 hP3