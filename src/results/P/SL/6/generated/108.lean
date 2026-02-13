

theorem interior_closure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A \ B) : Set X)) ⊆ interior (closure A) := by
  -- `A \ B` is contained in `A`.
  have hSub : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Therefore, the closure of `A \ B` is contained in the closure of `A`.
  have hClSub : closure ((A \ B) : Set X) ⊆ closure A :=
    closure_mono hSub
  -- Apply monotonicity of `interior` to obtain the desired inclusion.
  exact interior_mono hClSub