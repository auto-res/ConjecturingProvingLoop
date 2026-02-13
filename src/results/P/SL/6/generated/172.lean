

theorem interior_closure_inter_interior_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ interior B) : Set X)) ⊆ interior (closure A) := by
  -- `A ∩ interior B` is contained in `A`.
  have hSub : (A ∩ interior B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Therefore, the closure of `A ∩ interior B` is contained in the closure of `A`.
  have hClSub : closure (A ∩ interior B : Set X) ⊆ closure A :=
    closure_mono hSub
  -- Applying monotonicity of `interior` yields the desired inclusion.
  exact interior_mono hClSub