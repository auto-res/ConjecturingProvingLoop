

theorem Topology.subset_closure_interior_of_subset_of_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    Topology.P1 A → B ⊆ A → B ⊆ closure (interior A) := by
  intro hP1 hSub x hxB
  exact hP1 (hSub hxB)