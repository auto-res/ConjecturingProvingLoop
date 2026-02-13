

theorem Topology.closure_interior_diff_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior (closure A)) := by
  exact
    Set.Subset.trans
      (Topology.closure_interior_diff_subset_closure_interior
        (X := X) (A := A) (B := B))
      (Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := A))