

theorem Topology.interiorClosureInterior_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  -- First, note that `interior A ⊆ A`.
  have h_subset : interior A ⊆ A := interior_subset
  -- Taking closures preserves inclusion, giving
  -- `closure (interior A) ⊆ closure A`.
  have h_closure : closure (interior A) ⊆ closure A :=
    closure_mono h_subset
  -- Applying monotonicity of `interior` to the previous inclusion
  -- yields the desired result.
  exact interior_mono h_closure