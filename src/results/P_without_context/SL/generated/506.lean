

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  unfold Topology.P2 Topology.P1
  intro hP2 x hxA
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  have : x ∈ closure (interior A) := interior_subset hx
  exact this