

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 A := by
  intro h
  unfold Topology.P2 Topology.P1 at *
  intro x hx
  have h' : x ∈ interior (closure (interior A)) := h hx
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) h'