

theorem Topology.P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (interior A) := by
  unfold Topology.P2
  intro x hx
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    have h₁ : interior A ⊆ closure (interior A) := subset_closure
    exact interior_maximal h₁ isOpen_interior
  simpa [interior_interior] using hsubset hx