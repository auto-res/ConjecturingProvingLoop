

theorem Topology.interiorClosure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure A) ⊆ closure A := by
  simpa using (interior_subset : interior (closure A) ⊆ closure A)