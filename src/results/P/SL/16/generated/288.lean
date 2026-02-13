

theorem Topology.interior_closure_inter_closure_subset_closure_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∩ closure B ⊆ closure (closure A ∩ B) := by
  simpa using
    (Topology.interior_inter_closure_subset_closure_inter
      (X := X) (A := closure A) (B := B))