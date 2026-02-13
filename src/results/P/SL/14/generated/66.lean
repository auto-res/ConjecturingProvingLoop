

theorem Topology.closureInterior_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  have h : (interior A : Set X) ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact closure_mono h