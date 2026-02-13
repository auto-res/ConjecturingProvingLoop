

theorem closure_interior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure A := by
  -- The interior of `A` is contained in `A`.
  have h : interior A ⊆ A := interior_subset
  -- Monotonicity of `closure` turns this into the desired inclusion.
  exact closure_mono h