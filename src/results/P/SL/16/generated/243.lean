

theorem Topology.P1_closure_iff_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (closure A) ↔
      closure A ⊆ closure (interior (closure A)) := by
  simpa using
    (Topology.P1_iff_closure_subset_closure_interior
      (X := X) (A := closure A))