

theorem Topology.closure_interior_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure A)) := by
  exact closure_interior_mono (subset_closure : A ⊆ closure A)