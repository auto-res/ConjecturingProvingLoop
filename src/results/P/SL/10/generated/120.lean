

theorem Topology.closure_interior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  have h_subset : interior A ⊆ A := interior_subset
  exact closure_minimal h_subset hA