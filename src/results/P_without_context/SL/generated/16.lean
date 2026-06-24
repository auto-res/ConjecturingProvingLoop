

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (A := A)) : Topology.P3 (A := A) := by
  dsimp [Topology.P2, Topology.P3] at *
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := h hx
  have h_sub : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have hx₂ : x ∈ interior (closure A) := (interior_mono h_sub) hx₁
  exact hx₂