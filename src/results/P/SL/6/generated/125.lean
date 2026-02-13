

theorem closure_interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A \ B) : Set X))
      ⊆ closure (interior A) := by
  -- First, note that `A \ B ⊆ A`.
  have hSub : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Monotonicity of `interior` lifts this inclusion.
  have hIntSub : interior ((A \ B) : Set X) ⊆ interior A :=
    interior_mono hSub
  -- Applying `closure` preserves the inclusion.
  exact closure_mono hIntSub