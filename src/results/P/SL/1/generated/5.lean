

theorem P1_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (closure A)) := by
  dsimp [Topology.P1]
  simpa using (subset_closure : interior (closure A) ⊆ closure (interior (closure A)))