

theorem Topology.closureInterior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) :
    closure (interior A) ⊆ A := by
  have h_subset : (interior A : Set X) ⊆ A := interior_subset
  exact closure_minimal h_subset hA_closed