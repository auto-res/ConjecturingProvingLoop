

theorem Topology.interior_closure_diff_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆ interior (closure A) := by
  -- The set difference `A \ B` is contained in `A`.
  have h₁ : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves inclusions.
  have h₂ : closure (A \ B : Set X) ⊆ closure A :=
    closure_mono h₁
  -- Finally, apply monotonicity of `interior`.
  exact interior_mono h₂