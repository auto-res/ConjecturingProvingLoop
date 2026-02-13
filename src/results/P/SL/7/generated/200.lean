

theorem Topology.closureInterior_subset_closureInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure (interior (closure (interior A))) := by
  -- First, note the basic inclusion `interior A ⊆ interior (closure (interior A))`.
  have h : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    Topology.interior_subset_interiorClosureInterior (A := A)
  -- Taking closures preserves inclusions, yielding the desired result.
  exact closure_mono h