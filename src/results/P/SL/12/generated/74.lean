

theorem Topology.interior_closure_interior_closure_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) ⊆ closure A := by
  simpa [closure_closure] using
    (Topology.interior_closure_interior_subset_closure
      (X := X) (A := closure A))