

theorem Topology.closureInterior_subset_closureInteriorClosure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  have h : interior A ⊆ interior (closure A) :=
    interior_mono subset_closure
  exact closure_mono h