

theorem closure_interior_diff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior A) := by
  -- First, note that `A \ B ⊆ A`.
  have h₁ : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Hence `interior (A \ B) ⊆ interior A` by monotonicity of `interior`.
  have h₂ : interior (A \ B : Set X) ⊆ interior A :=
    interior_mono h₁
  -- Taking closures preserves inclusions.
  exact closure_mono h₂