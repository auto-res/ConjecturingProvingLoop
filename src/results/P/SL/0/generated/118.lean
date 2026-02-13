

theorem P2_implies_closure_subset_closure_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      closure (A : Set X) ⊆ closure (interior (closure (interior A))) := by
  intro hP2
  dsimp [Topology.P2] at hP2
  exact closure_mono hP2