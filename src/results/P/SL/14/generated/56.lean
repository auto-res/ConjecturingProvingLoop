

theorem Topology.closureInteriorClosure_subset_closure' {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  have h : interior (closure A) ⊆ closure A := interior_subset
  simpa [closure_closure] using closure_mono h