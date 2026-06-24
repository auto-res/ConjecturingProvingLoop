

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  dsimp [Topology.P2] at h
  dsimp [Topology.P1]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h hx
  have : x ∈ closure (interior A) := interior_subset hx'
  exact this