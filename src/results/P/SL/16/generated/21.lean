

theorem Topology.P1_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure A)) := by
  dsimp [Topology.P1]
  intro x hx
  have : x ∈ closure (interior (closure A)) := subset_closure hx
  simpa [interior_interior] using this