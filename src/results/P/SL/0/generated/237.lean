

theorem interior_closure_inter_left_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ interior (B : Set X)) : Set X)) ⊆
      interior (closure (A : Set X)) := by
  -- `A ∩ interior B` is contained in `A`.
  have hSub : (A ∩ interior (B : Set X) : Set X) ⊆ (A : Set X) := by
    intro x hx
    exact hx.1
  -- Apply monotonicity of `closure` and then of `interior`.
  exact interior_mono (closure_mono hSub)