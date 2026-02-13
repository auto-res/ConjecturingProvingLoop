

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (A : Set X)) := by
  dsimp [Topology.P1]
  intro x hx
  simpa [interior_interior] using (subset_closure hx)