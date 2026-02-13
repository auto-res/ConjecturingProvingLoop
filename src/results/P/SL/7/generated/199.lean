

theorem Topology.P3_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → A ⊆ closure A := by
  intro hP3
  dsimp [Topology.P3] at hP3
  intro x hxA
  have : x ∈ interior (closure A) := hP3 hxA
  exact interior_subset this