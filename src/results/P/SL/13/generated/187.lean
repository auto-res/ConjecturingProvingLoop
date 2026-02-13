

theorem Topology.interior_closure_interior_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) ⊆
      closure (interior (closure (A : Set X))) := by
  intro x hx
  exact
    (interior_subset :
      interior (closure (interior (closure (A : Set X)))) ⊆
        closure (interior (closure (A : Set X)))) hx