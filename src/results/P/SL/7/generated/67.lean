

theorem Topology.closureInteriorClosureInterior_eq_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) = closure (interior A) := by
  apply Set.Subset.antisymm
  ·
    have h : interior (closure (interior A)) ⊆ closure (interior A) := by
      exact interior_subset
    have h' := closure_mono h
    simpa [closure_closure] using h'
  ·
    have h : interior A ⊆ interior (closure (interior A)) :=
      Topology.interior_subset_interiorClosureInterior (A := A)
    have h' := closure_mono h
    simpa [closure_closure] using h'