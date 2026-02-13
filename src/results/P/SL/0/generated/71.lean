

theorem P3_implies_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (A : Set X) ⊆ interior (closure (A : Set X)) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  simpa using hP3