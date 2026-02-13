

theorem Topology.P1_of_subset_of_subset_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hBClA : B ⊆ closure A)
    (hP1A : Topology.P1 (A := A)) : Topology.P1 (A := B) := by
  dsimp [Topology.P1] at hP1A ⊢
  intro x hxB
  -- `x ∈ closure A` since `B ⊆ closure A`
  have hx_closureA : x ∈ closure A := hBClA hxB
  -- `closure A = closure (interior A)` by `P1` for `A`
  have hClosEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1A
  -- Rewrite membership using this equality
  have hx_closureIntA : x ∈ closure (interior A) := by
    simpa [hClosEq] using hx_closureA
  -- Monotonicity from `interior A ⊆ interior B`
  have hIntAB : interior A ⊆ interior B := interior_mono hAB
  have hClosIntAB : closure (interior A) ⊆ closure (interior B) :=
    closure_mono hIntAB
  -- Conclude the goal
  exact hClosIntAB hx_closureIntA