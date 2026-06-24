

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 (A := A) := by
  intro hP2
  unfold Topology.P2 at hP2
  unfold Topology.P1
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := hP2 hx
  exact (interior_subset) hx'