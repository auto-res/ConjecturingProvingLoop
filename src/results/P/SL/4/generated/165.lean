

theorem interior_diff_subset_interior {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B) ⊆ interior A := by
  -- `A \ B` is contained in `A`.
  have h_sub : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Monotonicity of `interior` gives the desired inclusion.
  exact interior_mono h_sub