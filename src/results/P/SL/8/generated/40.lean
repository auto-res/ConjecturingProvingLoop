

theorem P3_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    A ⊆ closure A := by
  dsimp [Topology.P3] at hP3
  exact Set.Subset.trans hP3 interior_subset