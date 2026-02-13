

theorem Topology.closure_interior_eq_of_P1_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) (hClosed : IsClosed A) :
    closure (interior A) = A := by
  apply Set.Subset.antisymm
  ·
    have h_subset : interior A ⊆ A := interior_subset
    exact closure_minimal h_subset hClosed
  ·
    exact hP1