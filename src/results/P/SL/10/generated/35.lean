

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure A := by
  intro x hx
  exact subset_closure (interior_subset hx)