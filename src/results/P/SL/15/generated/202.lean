

theorem P1_subset_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → A ⊆ closure (interior A) := by
  intro hP1
  simpa [Topology.P1] using hP1