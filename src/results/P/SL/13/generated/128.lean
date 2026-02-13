

theorem Topology.closure_interior_diff_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A \ B) : Set X)) ⊆ closure (interior A) := by
  intro x hx
  -- `A \ B` is contained in `A`
  have h_subset : ((A \ B) : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  -- Monotonicity of `interior`
  have h_interior : interior ((A \ B) : Set X) ⊆ interior A :=
    interior_mono h_subset
  -- Monotonicity of `closure`
  have h_closure :
      closure (interior ((A \ B) : Set X)) ⊆ closure (interior A) :=
    closure_mono h_interior
  exact h_closure hx