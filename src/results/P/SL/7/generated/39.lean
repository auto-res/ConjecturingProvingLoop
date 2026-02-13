

theorem Topology.closureInterior_subset_closureInteriorClosure {X : Type*} [TopologicalSpace X]
    (A : Set X) : closure (interior A) ⊆ closure (interior (closure A)) := by
  exact closure_mono (interior_mono subset_closure)