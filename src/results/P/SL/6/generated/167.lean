

theorem closure_interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (A : Set X)))) ⊆
      closure (interior (closure A)) := by
  exact
    closure_mono
      (Topology.interior_closure_interior_subset_closure (A := A))