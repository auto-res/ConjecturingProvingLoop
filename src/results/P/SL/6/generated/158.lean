

theorem subset_interior_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → (A : Set X) ⊆ interior (closure (interior A)) := by
  intro hP2
  dsimp [Topology.P2] at hP2
  exact hP2