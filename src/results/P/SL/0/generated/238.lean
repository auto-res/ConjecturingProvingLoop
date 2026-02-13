

theorem closure_subset_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A →
      closure (A : Set X) ⊆
        closure (interior (closure (A : Set X))) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  exact closure_mono hP3