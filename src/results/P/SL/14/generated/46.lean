

theorem Topology.closureInteriorClosure_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure A)) ⊆ closure A := by
  simpa [closure_closure] using
    (closure_mono (interior_subset : interior (closure A) ⊆ closure A))