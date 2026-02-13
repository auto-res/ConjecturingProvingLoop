

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  exact
    Set.Subset.trans
      (Topology.interior_closure_interior_subset_closure_interior
        (X := X) (A := A))
      (Topology.closure_interior_subset_closure_interior_closure
        (X := X) (A := A))