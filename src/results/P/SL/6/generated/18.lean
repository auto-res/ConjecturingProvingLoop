

theorem interior_closure_satisfies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure (A : Set X))) := by
  dsimp [Topology.P1]
  simpa using
    (subset_closure :
      interior (closure (A : Set X)) ⊆ closure (interior (closure A)))