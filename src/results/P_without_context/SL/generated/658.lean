

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2] at hP2
  dsimp [Topology.P1]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hP2 hx
  have h_subset : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact h_subset hx'