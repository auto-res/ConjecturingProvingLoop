

theorem closure_subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (A : Set X) →
      closure (A : Set X) ⊆ closure (interior (A : Set X)) := by
  intro hP1
  exact closure_minimal hP1 isClosed_closure