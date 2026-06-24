

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 A) : Topology.P1 A := by
  intro x hx
  have hx₁ : x ∈ interior (closure (interior A)) := h hx
  have hx₂ : x ∈ closure (interior A) := interior_subset hx₁
  exact hx₂