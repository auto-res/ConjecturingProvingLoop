

theorem Topology.interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ⊆ interior (closure A) := by
  exact interior_mono subset_closure