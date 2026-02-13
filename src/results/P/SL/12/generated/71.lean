

theorem Topology.interior_closure_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆ closure A := by
  exact interior_subset