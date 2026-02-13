

theorem Topology.interior_closure_interior_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  -- First, note that `interior A ⊆ A`.
  have h₁ : interior A ⊆ A := interior_subset
  -- Taking closures preserves this inclusion.
  have h₂ : closure (interior A) ⊆ closure A := closure_mono h₁
  -- Finally, apply monotonicity of `interior`.
  exact interior_mono h₂