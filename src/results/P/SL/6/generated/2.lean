

theorem interior_satisfies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior A) := by
  dsimp [Topology.P1]
  simpa using (subset_closure : interior A ⊆ closure (interior A))