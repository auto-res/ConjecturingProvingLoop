

theorem Topology.closure_interior_subset_closed_iff {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    closure (interior A) ⊆ B ↔ interior A ⊆ B := by
  constructor
  · intro h_subset
    exact
      Set.Subset.trans
        (subset_closure : interior A ⊆ closure (interior A)) h_subset
  · intro h_int_subset
    exact closure_minimal h_int_subset hB