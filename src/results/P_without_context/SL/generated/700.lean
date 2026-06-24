

theorem Topology.P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P3 (A := A) := by
  dsimp [Topology.P2, Topology.P3] at *
  intro x hxA
  have hx₁ : x ∈ interior (closure (interior A)) := h hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have hcl : closure (interior A) ⊆ closure A := closure_mono interior_subset
    exact interior_mono hcl
  exact hsubset hx₁