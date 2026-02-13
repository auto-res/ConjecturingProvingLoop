

theorem Topology.interior_closure_diff_subset_interior_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A \ B) : Set X)) ⊆ interior (closure A) := by
  intro x hx
  -- First, note that `A \ B ⊆ A`.
  have h_subset : ((A \ B) : Set X) ⊆ A := by
    intro y hy
    exact hy.1
  -- Taking closures preserves this inclusion.
  have h_closure : closure ((A \ B) : Set X) ⊆ closure A :=
    closure_mono h_subset
  -- Finally, apply monotonicity of `interior`.
  exact (interior_mono h_closure) hx