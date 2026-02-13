

theorem Topology.interiorClosure_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A \ B : Set X)) ⊆ interior (closure A) := by
  -- `A \ B` is contained in `A`.
  have h_subset : (A \ B : Set X) ⊆ A := by
    intro x hx
    exact hx.1
  -- Taking closures preserves the inclusion.
  have h_closure_subset :
      closure (A \ B : Set X) ⊆ closure A := closure_mono h_subset
  -- Monotonicity of `interior` then yields the desired inclusion.
  exact interior_mono h_closure_subset