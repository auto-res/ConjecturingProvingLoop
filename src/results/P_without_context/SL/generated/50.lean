

theorem P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A := A) → Topology.P1 A := by
  intro h
  dsimp [Topology.P2] at h
  dsimp [Topology.P1]
  intro x hxA
  have hxint : x ∈ interior (closure (interior A)) := h hxA
  have hsub : interior (closure (interior A)) ⊆ closure (interior A) := by
    intro y hy
    exact interior_subset hy
  exact hsub hxint