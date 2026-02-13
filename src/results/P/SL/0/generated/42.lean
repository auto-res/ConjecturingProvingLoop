

theorem closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) ⊆ closure (interior (closure (A : Set X))) := by
  -- Since `A ⊆ closure A`, monotonicity of `interior` gives the key inclusion.
  have h : interior (A : Set X) ⊆ interior (closure (A : Set X)) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure (A : Set X))
  -- Taking `closure` on both sides preserves the inclusion.
  exact closure_mono h