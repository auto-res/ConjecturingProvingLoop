

theorem Topology.interior_eq_of_P3_and_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 A) (hClosed : IsClosed A) :
    interior A = A := by
  apply Set.Subset.antisymm
  · exact interior_subset
  ·
    have : A ⊆ interior (closure A) := hP3
    simpa [hClosed.closure_eq] using this