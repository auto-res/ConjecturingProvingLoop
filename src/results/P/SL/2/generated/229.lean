

theorem Topology.interior_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (A : Set X) := by
  intro x hxInt
  exact subset_closure (interior_subset hxInt)