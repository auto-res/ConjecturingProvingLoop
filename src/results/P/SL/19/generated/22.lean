

theorem Topology.P1_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A := interior (closure A)) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)