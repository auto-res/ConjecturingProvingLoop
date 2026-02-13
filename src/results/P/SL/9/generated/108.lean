

theorem Topology.interiorClosureInterior_subset_interiorClosureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆
      interior (closure (interior (closure A))) := by
  -- `interior A` is contained in `interior (closure A)`.
  have h_int : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  -- Taking closures preserves this inclusion.
  have h_closure : closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono h_int
  -- Applying monotonicity of `interior` once more yields the result.
  exact interior_mono h_closure