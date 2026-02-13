

theorem interior_closure_inter_right_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((interior (A : Set X) ∩ B) : Set X)) ⊆
      interior (closure (B : Set X)) := by
  -- The set `interior A ∩ B` is contained in `B`.
  have hSub : (interior (A : Set X) ∩ B : Set X) ⊆ (B : Set X) := by
    intro x hx
    exact hx.2
  -- Monotonicity of `closure` and then of `interior` yields the result.
  exact interior_mono (closure_mono hSub)