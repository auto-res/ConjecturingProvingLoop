

theorem Topology.closure_interior_diff_subset_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior A) := by
  -- First, note that `A \ B ⊆ A`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Monotonicity of `interior` transports this inclusion.
  have h_int_subset : interior (A \ B : Set X) ⊆ interior A :=
    interior_mono h_subset
  -- Finally, taking closures preserves inclusions.
  exact closure_mono h_int_subset