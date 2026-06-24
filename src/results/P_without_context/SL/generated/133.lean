

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  dsimp [Topology.P2, Topology.P1] at *
  intro x hxA
  have hx1 : x ∈ interior (closure (interior A)) := hP2 hxA
  have hx2 : x ∈ closure (interior A) := interior_subset hx1
  exact hx2