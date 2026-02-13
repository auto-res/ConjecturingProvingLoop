

theorem Topology.boundary_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (A : Set X) \ interior A) ⊆ closure A := by
  intro x hx
  exact hx.1