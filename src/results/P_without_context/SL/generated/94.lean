

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P3 A :=
by
  intro h
  dsimp [Topology.P2, Topology.P3] at h ⊢
  intro x hxA
  have hx : x ∈ interior (closure (interior A)) := h hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
    interior_mono (closure_mono (interior_subset : interior A ⊆ A))
  exact hsubset hx