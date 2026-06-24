

theorem P2_implies_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) A) : Topology.P1 (X := X) A := by
  dsimp [Topology.P2, Topology.P1] at *
  intro x hxA
  have hx' : x ∈ interior (closure (interior A)) := h hxA
  have hsubset : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  exact hsubset hx'