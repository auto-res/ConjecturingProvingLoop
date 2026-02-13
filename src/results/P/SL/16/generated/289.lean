

theorem Topology.interior_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ⊆ closure (interior A) := by
  intro x hxInt
  exact subset_closure hxInt