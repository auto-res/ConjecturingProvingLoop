

theorem P2_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P3 (A := A) := by
  dsimp [Topology.P3, Topology.P2] at *
  intro x hx
  have hx0 : x ∈ interior (closure (interior A)) := h hx
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    apply interior_mono
    apply closure_mono
    exact interior_subset
  exact hsubset hx0