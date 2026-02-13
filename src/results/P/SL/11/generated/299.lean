

theorem subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A ⊆ closure (interior A)) := by
  intro hP1
  exact hP1