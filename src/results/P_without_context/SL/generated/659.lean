

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P1] at hP2 ⊢
  intro x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  exact interior_subset hx