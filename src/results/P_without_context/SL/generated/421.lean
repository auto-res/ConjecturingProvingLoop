

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
  Topology.P2 A → Topology.P3 A := by
  intro h2
  dsimp [Topology.P2] at h2
  dsimp [Topology.P3]
  intro x hx
  have hx' : x ∈ interior (closure (interior A)) := h2 hx
  have h_subset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono (interior_subset : interior A ⊆ A))
  exact h_subset hx'