

theorem Topology.P1_iff_closureInterior_eq_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Topology.P1 A ↔ closure (interior A) = A := by
  dsimp [Topology.P1]
  constructor
  · intro hP1
    have h_subset : closure (interior A) ⊆ A :=
      closure_minimal (interior_subset : interior A ⊆ A) hA_closed
    exact Set.Subset.antisymm h_subset hP1
  · intro h_eq
    simpa [h_eq] using (subset_rfl : (A : Set X) ⊆ A)