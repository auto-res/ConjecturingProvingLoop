

theorem Topology.boundary_subset_closure_left {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A \ interior A ⊆ closure A := by
  intro x hx
  exact hx.1