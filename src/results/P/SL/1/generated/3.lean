

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (interior A) := by
  dsimp [Topology.P3]
  have h : interior (interior A) ⊆ interior (closure (interior A)) := by
    apply interior_mono
    intro x hx
    exact subset_closure hx
  simpa [interior_interior] using h