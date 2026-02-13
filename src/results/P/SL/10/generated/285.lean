

theorem Topology.closure_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ closure B) ⊆ closure A ∩ closure B := by
  simpa [closure_closure] using
    (Topology.closure_inter_subset_inter_closure
      (X := X) (A := A) (B := closure B))