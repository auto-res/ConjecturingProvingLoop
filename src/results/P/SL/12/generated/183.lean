

theorem Topology.closure_interior_diff_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior A) := by
  -- `A \ B` is a subset of `A`.
  have h_subset : (A \ B : Set X) ⊆ A := Set.diff_subset
  -- Apply monotonicity of `interior` to the subset inclusion.
  have h_int : (interior (A \ B : Set X) : Set X) ⊆ interior A :=
    interior_mono h_subset
  -- Take closures to obtain the desired inclusion.
  exact closure_mono h_int