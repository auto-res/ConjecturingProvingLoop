

theorem Topology.closureInterior_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior A) ⊆ closure (A : Set X) := by
  simpa using
    closure_mono (interior_subset : interior A ⊆ A)