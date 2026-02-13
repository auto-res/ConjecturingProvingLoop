

theorem P1_of_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) := by
  dsimp [Topology.P1]
  simpa [interior_interior] using
    (subset_closure : interior (closure A) ⊆ closure (interior (closure A)))