

theorem Topology.interior_closure_subset_closureInterior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) ⊆ closure (interior (closure (A : Set X))) := by
  intro x hx
  exact subset_closure hx