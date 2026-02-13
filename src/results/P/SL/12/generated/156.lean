

theorem Topology.interior_diff_subset_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior A := by
  simpa using
    interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)