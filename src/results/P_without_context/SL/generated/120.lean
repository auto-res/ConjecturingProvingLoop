

theorem P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 A := by
  intro h
  dsimp [Topology.P2, Topology.P1] at h ⊢
  intro x hx
  have hxInt : x ∈ interior (closure (interior A)) := h hx
  have hInc : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hInc hxInt