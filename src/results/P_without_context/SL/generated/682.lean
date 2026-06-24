

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P1, Topology.P2] at hP2 ⊢
  intro x hxA
  have hInt : x ∈ interior (closure (interior A)) := hP2 hxA
  exact
    (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hInt