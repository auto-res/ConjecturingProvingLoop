

theorem Topology.interior_closure_interior_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  exact interior_subset