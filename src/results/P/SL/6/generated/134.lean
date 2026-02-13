

theorem subset_interior_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A : Set X) → (A : Set X) ⊆ interior (closure A) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  exact hP3