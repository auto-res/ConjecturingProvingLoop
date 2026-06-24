

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  intro x hxA
  have hx_int : x ∈ interior (closure (interior A)) := hP2 hxA
  exact interior_subset hx_int