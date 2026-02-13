

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  exact Set.Subset.trans interior_subset subset_closure