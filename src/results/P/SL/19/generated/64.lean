

theorem Topology.closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  simpa using
    (closure_mono
      (interior_subset : interior (closure A) ⊆ closure A))