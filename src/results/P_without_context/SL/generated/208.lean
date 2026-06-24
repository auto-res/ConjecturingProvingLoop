

theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro hP2
  unfold Topology.P2 at hP2
  unfold Topology.P1
  intro x hx
  have hx_in : x ∈ interior (closure (interior A)) := hP2 hx
  have hsub : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  exact hsub hx_in