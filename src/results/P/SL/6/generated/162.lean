

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) ⊆ interior (closure A) := by
  -- From `interior A ⊆ A`, taking closures preserves the inclusion.
  have h : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset : interior (A : Set X) ⊆ A)
  -- Applying monotonicity of `interior` yields the desired result.
  exact interior_mono h